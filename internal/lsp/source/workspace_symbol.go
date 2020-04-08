// Copyright 2020 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package source

import (
	"context"
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"sort"
	"strconv"
	"strings"

	"golang.org/x/tools/internal/event"
	"golang.org/x/tools/internal/lsp/fuzzy"
	"golang.org/x/tools/internal/lsp/protocol"
	"golang.org/x/tools/internal/span"
	errors "golang.org/x/xerrors"
)

// maxSymbols defines the maximum number of protocol.SymbolInformation results
// that should ever be sent in response to a client
const maxSymbols = 100

type symbolOption string

const (
	optionSeparator                                   = "::"
	symbolOptionStructFields             symbolOption = "structFields"
	symbolOptionInterfaceMethods         symbolOption = "interfaceMethods"
	symbolOptionKind                     symbolOption = "kind"
	symbolOptionPackageOnly              symbolOption = "packageOnly"
	symbolOptionWorkspaceOnly            symbolOption = "workspaceOnly"
	symbolOptionNonWorkspaceExportedOnly symbolOption = "nonWorkspaceExportedOnly"
)

// WorkspaceSymbols matches symbols across views using the given query,
// according to the SymbolMatcher matcher.
//
// The workspace symbol method is defined in the spec as follows:
//
//  > The workspace symbol request is sent from the client to the server to
//  > list project-wide symbols matching the query string.
//
// It is unclear what "project-wide" means here, but given the parameters of
// workspace/symbol do not include any workspace identifier, then it has to be
// assumed that "project-wide" means "across all workspaces".  Hence why
// WorkspaceSymbols receives the views []View.
//
// However, it then becomes unclear what it would mean to call WorkspaceSymbols
// with a different configured SymbolMatcher per View. Therefore we assume that
// Session level configuration will define the SymbolMatcher to be used for the
// WorkspaceSymbols method.
func WorkspaceSymbols(ctx context.Context, matcherType SymbolMatcher, views []View, query string) ([]protocol.SymbolInformation, error) {
	ctx, done := event.Start(ctx, "source.WorkspaceSymbols")
	defer done()
	if query == "" {
		return nil, nil
	}
	sc := newSymbolCollector(ctx, matcherType, query, views)
	return sc.walk()
}

// symbolCollector is a convenience type for holding context as we walk the
// View instances (ultimately Package instances) gathering symbols that match a
// given query
type symbolCollector struct {
	ctx context.Context

	// query is the user-supplied query passed to the Symbol method
	query string

	// views are the View instances to walk
	views []View

	// currView is the View we are currently walking
	currView View

	// currPkg is the Package we are currently walking
	currPkg Package

	// matcher is the symbolMatcher used to gather matches as we walk
	matcher symbolMatcher

	// seen is a map of the symbols we have already visited. See the comment for
	// viewsToPackages
	seen map[symbolInformation]bool

	// options
	workspaceOnly            bool
	nonWorkspaceExportedOnly bool
	packageOnly              *string
	kinds                    map[protocol.SymbolKind]bool
	structFields             bool
	interfaceMethods         bool

	exportedOnly bool
}

func newSymbolCollector(ctx context.Context, matcher SymbolMatcher, query string, views []View) *symbolCollector {
	res := &symbolCollector{
		ctx:   ctx,
		views: views,
		seen:  make(map[symbolInformation]bool),

		// option defaults
		structFields:     true,
		interfaceMethods: true,
	}
	// Parse options
	var queryParts []string
	for _, part := range strings.Fields(query) {
		if ok, v := tokenIsOption(part, symbolOptionWorkspaceOnly); ok {
			if b, err := strconv.ParseBool(v); err == nil {
				res.workspaceOnly = b
			}
			continue
		}
		if ok, v := tokenIsOption(part, symbolOptionNonWorkspaceExportedOnly); ok {
			if b, err := strconv.ParseBool(v); err == nil {
				res.nonWorkspaceExportedOnly = b
			}
			continue
		}
		if ok, v := tokenIsOption(part, symbolOptionPackageOnly); ok {
			res.packageOnly = &v
			continue
		}
		if ok, v := tokenIsOption(part, symbolOptionKind); ok {
			parts := strings.Split(v, ",")
			res.kinds = make(map[protocol.SymbolKind]bool)
			for _, k := range parts {
				res.kinds[protocol.ParseSymbolKind(k)] = true
			}
			continue
		}
		if ok, v := tokenIsOption(part, symbolOptionStructFields); ok {
			if b, err := strconv.ParseBool(v); err == nil {
				res.structFields = b
			}
			continue
		}
		if ok, v := tokenIsOption(part, symbolOptionInterfaceMethods); ok {
			if b, err := strconv.ParseBool(v); err == nil {
				res.interfaceMethods = b
			}
			continue
		}
		queryParts = append(queryParts, part)
	}
	query = strings.Join(queryParts, " ")

	// Setup matcher
	var m symbolMatcher
	switch matcher {
	case SymbolFuzzy:
		m = newFuzzySymbolMatcher(query)
	case SymbolCaseInsensitive:
		m = newCaseBasedSymbolMatcher(false, query)
	case SymbolCaseSensitive:
		m = newCaseBasedSymbolMatcher(true, query)
	default:
		panic(fmt.Errorf("unkown Matcher type: %v", matcher))
	}
	res.matcher = m

	return res
}

// walk walks sc.views gathering symbols and returns the results
func (sc *symbolCollector) walk() (_ []protocol.SymbolInformation, err error) {
	toWalk, err := sc.viewsToPackages()
	if err != nil {
		return nil, err
	}
	defer func() {
		switch r := recover().(type) {
		case nil:
		case knownSymbolError:
			if r != earlySymbolWalkExit {
				err = r
			}
		default:
			panic(r)
		}
	}()
	for _, pv := range toWalk {
		sc.currPkg = pv.pkg
		sc.currView = pv.view
		sc.exportedOnly = sc.nonWorkspaceExportedOnly && !pv.isWorkspace
		for _, fh := range pv.pkg.CompiledGoFiles() {
			file, _, _, _, err := fh.Cached()
			sc.check(err, "failed to get Cached file handle: %v", err)
			sc.walkFilesDecls(file.Decls, pv.pkg.PkgPath())
		}
	}
	return sc.matcher.results(), nil
}

// viewsToPackages gathers the packages we are going to inspect for symbols.
// This pre-step is required in order to filter out any "duplicate"
// *types.Package. The duplicates arise for packages that have test variants.
// For example, if package mod.com/p has test files, then we will visit two
// packages that have the PkgPath() mod.com/p: the first is the actual package
// mod.com/p, the second is a special version that includes the non-XTest
// _test.go files. If we were to walk both of of these packages, then we would
// get duplicate matching symbols and we would waste effort. Therefore where
// test variants exist we walk those (because they include any symbols defined
// in non-XTest _test.go files)
//
// One further complication is that even after this filtering, packages between
// views might not be "identical" because they can be built using different
// build constraints (via the "env" config option).
//
// Therefore on a per view basis we first build up a map of PkgPath() ->
// *types.Package preferring the test variants if they exist. Then we merge the
// results between views, de-duping by *types.Package.
//
// Finally, when we come to walk these packages and start gathering symbols, we
// ignore any symbols we have already seen (different *types.Package for the
// same import path because of different build constraints), keeping track of
// those symbols via symbolCollector.seen.
func (sc *symbolCollector) viewsToPackages() (toWalk []*pkgView, err error) {
	gather := make(map[string]map[*types.Package]*pkgView)
	for _, v := range sc.views {
		snap := v.Snapshot()

		seen := make(map[string]*pkgView)
		var forTests []*pkgView
		var err error
		var knownPkgs []PackageHandle
		if sc.packageOnly != nil {
			fh, err := snap.GetFile(sc.ctx, span.URI(*sc.packageOnly))
			if err != nil {
				// Not in this view
				continue
			}
			knownPkgs, err = snap.PackageHandles(sc.ctx, fh)
		} else if sc.workspaceOnly {
			knownPkgs, err = snap.WorkspacePackages(sc.ctx)
		} else {
			knownPkgs, err = snap.KnownPackages(sc.ctx)
		}
		if err != nil {
			return nil, err
		}
		var isWorkspacePkg map[PackageHandle]bool
		if !sc.workspaceOnly {
			workspacePackages, err := snap.WorkspacePackages(sc.ctx)
			if err != nil {
				return nil, err
			}
			isWorkspacePkg = make(map[PackageHandle]bool)
			for _, wp := range workspacePackages {
				isWorkspacePkg[wp] = true
			}
		}
		for _, ph := range knownPkgs {
			pkg, err := ph.Check(sc.ctx)
			if err != nil {
				return nil, err
			}
			toAdd := &pkgView{
				pkg:         pkg,
				view:        v,
				isWorkspace: sc.workspaceOnly || isWorkspacePkg[ph],
			}
			if pkg.ForTest() != "" {
				forTests = append(forTests, toAdd)
			} else {
				seen[pkg.PkgPath()] = toAdd
			}
		}
		for _, pkg := range forTests {
			seen[pkg.pkg.PkgPath()] = pkg
		}
		for _, pkg := range seen {
			pm, ok := gather[pkg.pkg.PkgPath()]
			if !ok {
				pm = make(map[*types.Package]*pkgView)
				gather[pkg.pkg.PkgPath()] = pm
			}
			pm[pkg.pkg.GetTypes()] = pkg
		}
	}
	for _, pm := range gather {
		for _, pkg := range pm {
			toWalk = append(toWalk, pkg)
		}
	}
	// Now sort for stability of results. We order by
	// (pkgView.isWorkspace, pkgView.v, pkgView.p.ID())
	sort.Slice(toWalk, func(i, j int) bool {
		lhs := toWalk[i]
		rhs := toWalk[j]
		var cmp int
		// workspace packages first
		switch {
		case lhs.isWorkspace == rhs.isWorkspace:
			cmp = 0
		case lhs.isWorkspace:
			cmp = -1
		case rhs.isWorkspace:
			cmp = 1
		}
		if cmp == 0 {
			var lhsIndex, rhsIndex int
			for i, v := range sc.views {
				if v == lhs.view {
					lhsIndex = i
				}
				if v == rhs.view {
					rhsIndex = i
				}
			}
			cmp = lhsIndex - rhsIndex
		}
		if cmp == 0 {
			cmp = strings.Compare(lhs.pkg.ID(), rhs.pkg.ID())
		}
		return cmp < 0
	})
	return
}

func tokenIsOption(token string, option symbolOption) (bool, string) {
	pref := string(option) + optionSeparator
	match := strings.HasPrefix(token, pref)
	return match, strings.TrimPrefix(token, pref)
}

func (sc *symbolCollector) walkFilesDecls(decls []ast.Decl, prefix string) {
	for _, decl := range decls {
		switch decl := decl.(type) {
		case *ast.FuncDecl:
			fn := decl.Name.Name
			kind := protocol.Function
			if decl.Recv != nil {
				kind = protocol.Method
				switch typ := decl.Recv.List[0].Type.(type) {
				case *ast.StarExpr:
					fn = typ.X.(*ast.Ident).Name + "." + fn
				case *ast.Ident:
					fn = typ.Name + "." + fn
				}
			}
			target := prefix + "." + fn
			if !sc.exportedOnly || decl.Name.IsExported() {
				sc.match(target, kind, decl.Name)
			}
		case *ast.GenDecl:
			for _, spec := range decl.Specs {
				switch spec := spec.(type) {
				case *ast.TypeSpec:
					target := prefix + "." + spec.Name.Name
					if !sc.exportedOnly || spec.Name.IsExported() {
						sc.match(target, typeToKind(sc.currPkg.GetTypesInfo().TypeOf(spec.Type)), spec.Name)
					}
					switch st := spec.Type.(type) {
					case *ast.StructType:
						if !sc.structFields {
							continue
						}
						for _, field := range st.Fields.List {
							sc.walkField(field, protocol.Field, target)
						}
					case *ast.InterfaceType:
						if !sc.interfaceMethods {
							continue
						}
						for _, field := range st.Methods.List {
							kind := protocol.Method
							if len(field.Names) == 0 {
								kind = protocol.Interface
							}
							sc.walkField(field, kind, target)
						}
					}
				case *ast.ValueSpec:
					for _, name := range spec.Names {
						target := prefix + "." + name.Name
						kind := protocol.Variable
						if decl.Tok == token.CONST {
							kind = protocol.Constant
						}
						if !sc.exportedOnly || name.IsExported() {
							sc.match(target, kind, name)
						}
					}
				}
			}
		}
	}
}

func (sc *symbolCollector) walkField(field *ast.Field, kind protocol.SymbolKind, prefix string) {
	if len(field.Names) == 0 {
		name := types.ExprString(field.Type)
		target := prefix + "." + name
		if !sc.exportedOnly || token.IsExported(name) {
			sc.match(target, kind, field)
		}
		return
	}
	for _, name := range field.Names {
		target := prefix + "." + name.Name
		if !sc.exportedOnly || name.IsExported() {
			sc.match(target, kind, name)
		}
	}
}

func typeToKind(typ types.Type) protocol.SymbolKind {
	switch typ := typ.Underlying().(type) {
	case *types.Interface:
		return protocol.Interface
	case *types.Struct:
		return protocol.Struct
	case *types.Signature:
		if typ.Recv() != nil {
			return protocol.Method
		}
		return protocol.Function
	case *types.Named:
		return typeToKind(typ.Underlying())
	case *types.Basic:
		i := typ.Info()
		switch {
		case i&types.IsNumeric != 0:
			return protocol.Number
		case i&types.IsBoolean != 0:
			return protocol.Boolean
		case i&types.IsString != 0:
			return protocol.String
		}
	}
	return protocol.Variable
}

// earlySymbolWalkExit is a sentinel error used by a symbolCollector or a
// symbolMatcher to cleanly exit the symbol walk early
var earlySymbolWalkExit = knownSymbolError{errors.New("early exit from symbol walk")}

// knownSymbolError is type used to wrap and distinguish errors we knowingly
// panic with from runtime panics. It is used by (*symbolCollector).walk()
type knownSymbolError struct {
	error
}

// check verifies that err is nil, panic-ing with a knownSymbolErr otherwise using
// format and args as inputs to fmt.Errorf. This gives symbol walking a trivial
// way to exit early on unexpected (but known) errors.
func (sc *symbolCollector) check(err error, format string, args ...interface{}) {
	if err != nil {
		panic(knownSymbolError{fmt.Errorf(format, args...)})
	}
}

// match finds matches and gathers the symbol identified by name, kind and node
// via the symbolCollector's matcher after first de-duping against previously
// seen symbols.
func (sc *symbolCollector) match(name string, kind protocol.SymbolKind, node ast.Node) {
	// TODO: improve the error handling here. These two calls seemingly
	// fail because of cgo related issues. For now we silently return, i.e.
	// skipping the attempt to add the match.
	mrng, err := posToMappedRange(sc.currView, sc.currPkg, node.Pos(), node.End())
	if err != nil {
		return
	}
	rng, err := mrng.Range()
	if err != nil {
		return
	}
	key := symbolInformation{
		Name: name,
		Kind: kind,
		Location: protocol.Location{
			URI:   protocol.URIFromSpanURI(mrng.URI()),
			Range: rng,
		},
	}
	if sc.seen[key] {
		return
	}
	sc.seen[key] = true
	if sc.kinds != nil {
		if !sc.kinds[kind] {
			return
		}
	}
	sc.matcher.gather(key)
}

// pkgView is a simple container for a Package, the View from which we gained a
// reference to the Package, and whether that Package is part of the workspace
// (i.e. is within the main module)
type pkgView struct {
	pkg         Package
	view        View
	isWorkspace bool
}

// symbolInformation is a cut-down version of protocol.SymbolInformation that
// allows struct values of this type to be used as map keys.
type symbolInformation struct {
	Name     string
	Kind     protocol.SymbolKind
	Location protocol.Location
}

// asProtocolSymbolInformation converts s to a protocol.SymbolInformation value
//
// TODO: work out how to handle tags if/when they are needed
func (s symbolInformation) asProtocolSymbolInformation() protocol.SymbolInformation {
	return protocol.SymbolInformation{
		Name:     s.Name,
		Kind:     s.Kind,
		Location: s.Location,
	}
}

// symbolMatcher defines the interface for a symbol matcher used by a symbolCollector
type symbolMatcher interface {
	gather(symbolInformation)
	results() []protocol.SymbolInformation
}

// caseBasedSymbolMatcher implements symbolMatcher for case-based matching of symbol
// names
type caseBasedSymbolMatcher struct {
	matcher func(string) bool
	res     []protocol.SymbolInformation
}

func newCaseBasedSymbolMatcher(caseSensitive bool, query string) *caseBasedSymbolMatcher {
	res := &caseBasedSymbolMatcher{}
	if caseSensitive {
		res.matcher = func(s string) bool {
			return strings.Contains(s, query)
		}
	} else {
		q := strings.ToLower(query)
		res.matcher = func(s string) bool {
			return strings.Contains(strings.ToLower(s), q)
		}
	}
	return res
}

func (c *caseBasedSymbolMatcher) gather(si symbolInformation) {
	if c.matcher(si.Name) {
		c.res = append(c.res, si.asProtocolSymbolInformation())
		if len(c.res) > maxSymbols {
			panic(earlySymbolWalkExit)
		}
	}
}

func (c *caseBasedSymbolMatcher) results() []protocol.SymbolInformation {
	return c.res
}

// caseBasedSymbolMatcher implements symbolMatcher for fuzzy matching of symbol
// names
type fuzzySymbolMatcher struct {
	fm  *fuzzy.Matcher
	res []scoredSymbolInformation
}

func newFuzzySymbolMatcher(query string) *fuzzySymbolMatcher {
	return &fuzzySymbolMatcher{
		fm: fuzzy.NewMatcher(query),
	}
}

func (f *fuzzySymbolMatcher) gather(si symbolInformation) {
	score := f.fm.Score(si.Name)
	if score > 0 {
		f.res = append(f.res, scoredSymbolInformation{
			symbolInformation: si,
			score:             score,
		})
	}
}

func (f *fuzzySymbolMatcher) results() (res []protocol.SymbolInformation) {
	sort.Slice(f.res, func(i, j int) bool {
		return f.res[i].score < f.res[j].score
	})
	pickFrom := f.res
	if len(pickFrom) > maxSymbols {
		pickFrom = pickFrom[:maxSymbols]
	}
	for _, si := range pickFrom {
		res = append(res, si.asProtocolSymbolInformation())
	}
	return
}

type scoredSymbolInformation struct {
	symbolInformation
	score float32
}
