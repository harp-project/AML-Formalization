import argparse
import typing as T


import pyk.kore.parser as KoreParser
import pyk.kore.syntax as Kore

class DefinitionError(Exception):
    pass

def get_all_imported_module_names(
    definition: Kore.Definition, module_name: str
) -> T.Set[str]:
    module = get_module_by_name(definition, module_name)
    names: T.Set[str] = set()
    for s in module.sentences:
        match s:
            case Kore.Import(imported_module_name, _):
                names.add(imported_module_name)
    return names


def get_all_recursively_imported_module_names(
    definition: Kore.Definition, module_name: str
) -> T.Set[str]:
    names: T.Set[str] = {module_name}
    new_names: T.Set[str] = {module_name}
    while len(new_names) > 0:
        curr_name = new_names.pop()
        names_to_add = get_all_imported_module_names(definition, curr_name).difference(
            names
        )
        names = names.union(names_to_add)
        new_names = new_names.union(names_to_add)
    return names


def get_module_by_name(definition: Kore.Definition, module_name: str) -> Kore.Module:
    for m in definition.modules:
        if m.name == module_name:
            return m

    # return None
    raise DefinitionError("Module '" + module_name + "' not found")

def sentences(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.Sentence]:
    module_names = {main_module_name}.union(
        get_all_recursively_imported_module_names(definition, main_module_name)
    )
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    sentences: T.List[Kore.Sentence] = []
    for m in modules:
        sentences.extend(m.sentences)
    return sentences

def is_sort_decl(s: Kore.Sentence) -> bool:
    match s:
        case Kore.SortDecl(_,_,_,_):
            return True
    return False

def is_symbol_decl(s: Kore.Sentence) -> bool:
    match s:
        case Kore.SymbolDecl(_, _, _, _, _):
            return True
    return False

def sort_decls(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.SortDecl]:
    return [s for s in sentences(definition, main_module_name) if is_sort_decl(s)] #type: ignore

def symbol_decls(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.SymbolDecl]:
    return [s for s in sentences(definition, main_module_name) if is_symbol_decl(s)] #type: ignore

def non_hooked_sort_names(definition: Kore.Definition, main_module_name: str, non_hooked_only: bool) -> T.Set[str]:
    sd = sort_decls(definition=definition, main_module_name=main_module_name)
    return {s.name for s in sd if not s.hooked or not non_hooked_only}

def non_hooked_symbol_names(definition: Kore.Definition, main_module_name: str, non_hooked_only: bool) -> T.Set[str]:
    sd = symbol_decls(definition=definition, main_module_name=main_module_name)
    return {s.symbol.name for s in sd if (not s.hooked or not non_hooked_only) and (Kore.App('impure') not in s.attrs)}

def get_symbol_decl_from_module(
    module: Kore.Module, symbol_name: str
) -> T.Optional[Kore.SymbolDecl]:
    for s in module.sentences:
        match s:
            case Kore.SymbolDecl(symbol, _, _, _, _):
                if symbol.name == symbol_name:
                    return s
    return None

def get_symbol_decl_from_definition(
    definition: Kore.Definition, main_module_name: str, symbol_name: str
) -> Kore.SymbolDecl:
    module_names = {main_module_name}.union(
        get_all_recursively_imported_module_names(definition, main_module_name)
    )
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    decls = [
        decl
        for decl in map(
            lambda module: get_symbol_decl_from_module(module, symbol_name), modules
        )
        if decl is not None
    ]
    if len(list(decls)) >= 1:
        return decls[0]
    raise DefinitionError(
        "No symbol '"
        + symbol_name
        + "' found in '"
        + main_module_name
        + "' (or recursively imported modules)"
    )


def get_symbol_sort(
    definition: Kore.Definition, main_module_name: str, symbol_name: str
) -> Kore.Sort:
    decl = get_symbol_decl_from_definition(definition, main_module_name, symbol_name)
    return decl.sort


def get_symbol_param_sorts(
    definition: Kore.Definition, main_module_name: str, symbol_name: str
) -> T.List[Kore.Sort]:
    decl = get_symbol_decl_from_definition(definition, main_module_name, symbol_name)
    return list(decl.param_sorts)

coq_preamble: str = '''
From Coq Require Import ssreflect ssrfun ssrbool.

From stdpp Require Import base finite list list_numbers strings propset.
(* This is unset by stdpp. We need to set it again.*)
Set Transparent Obligations.

From Equations Require Import Equations.
(* Set Equations Transparent. *)

From MatchingLogic.Utils Require Import Surj.
From MatchingLogic.OPML Require Import OpmlSignature OpmlModel.
'''

def inductive_from_names(name_of_inductive: str, names: T.List[str]) -> str:
    inductive_definition = f'''
    Inductive {name_of_inductive} :=
    {" ".join([f'| {s}' for s in names])}
    .
    '''
    return inductive_definition

def inductive_sorts(sort_names: T.List[str]) -> str:
    return inductive_from_names(name_of_inductive="Sort", names=sort_names)

def eqdec_finite(inductive_name: str, names: T.List[str]) -> str:
    helpers = f'''
    #[global]
    Instance {inductive_name}_eqdec: EqDecision {inductive_name}.
    Proof.
        solve_decision.
    Defined.
    '''
    helpers += f'''
    #[global]
    Program Instance {inductive_name}_finite: Finite {inductive_name} :=
    '''
    
    helpers += '''{|
        enum := [
    '''
    
    helpers += ('; '.join(names)) + '''];
    |}.
    Next Obligation.
        compute_done.
    Qed.
    Next Obligation.
        destruct x; compute_done.
    Qed.
    '''
    return helpers


def inductive_sorts_helpers(sort_names: T.List[str]) -> str:
    helpers = eqdec_finite("Sort", sort_names)
    helpers += '''
    Program Definition Sorts : OPMLSorts := {|
        opml_sort := Sort ;
        opml_subsort := eq ;
    |}.
    Next Obligation.
        repeat split.
        {
            intros x y z Hxy Hyz.
            subst. reflexivity.
        }
        {
            intros x y Hxy Hyx.
            subst. reflexivity.
        }
    Qed.

    Definition Vars : @OPMLVariables Sorts := {|
        opml_evar := fun s => string;
        opml_svar := fun s => string;
    |}.
    '''
    return helpers


def inductive_symbols(symbol_names: T.List[str]) -> str:
    return inductive_from_names(name_of_inductive="Symbols", names=symbol_names)

def mangle_even_more(s: str) -> str:
    return s.replace('-', "'DASH'")

def symbols_return_sorts(inductive_name: str, symbol_names: T.List[str], definition: Kore.Definition, main_module_name: str) -> str:
    s = f'''
    Definition {inductive_name}_return_sort (s : {inductive_name}) :=
        match s with
    '''
    symbol_sorts = [
        (
            mangle_even_more(symbol_name),
            mangle_even_more(
                get_symbol_sort(definition=definition, main_module_name=main_module_name, symbol_name=symbol_name).name
            )
        )
        for symbol_name in symbol_names
    ]
    s += "\n".join([f'| {symbol_name} => {return_sort}' for (symbol_name,return_sort) in symbol_sorts])
    s += '''
        end 
    .
    '''
    return s


def symbols_arg_sorts(inductive_name: str, symbol_names: T.List[str], definition: Kore.Definition, main_module_name: str) -> str:
    s = f'''
    Definition {inductive_name}_arg_sorts (s : {inductive_name}) :=
        match s with
    '''
    symbol_sorts = [
        (
            mangle_even_more(symbol_name),
            "[" + "; ".join([
                mangle_even_more(arg_sort.name)
                for arg_sort in
                get_symbol_param_sorts(definition=definition, main_module_name=main_module_name, symbol_name=symbol_name)
            ]) + "]"
        )
        for symbol_name in symbol_names
    ]
    s += "\n".join([f'| {symbol_name} => {arg_sorts}' for (symbol_name,arg_sorts) in symbol_sorts])
    s += '''
        end 
    .
    '''
    return s

def generate(input_kore_filename: str, main_module_name: str, output_v_filename: str):
    print(f'{input_kore_filename} > {output_v_filename}')
    parser = KoreParser.KoreParser(open(input_kore_filename).read())
    definition = parser.definition()
    sort_names: T.List[str] = list(non_hooked_sort_names(definition=definition, main_module_name=main_module_name, non_hooked_only=False))
    # TODO we should filter them by the attribute that is on the `inj` symbol, rather then by the name itself.
    symbol_names: T.List[str] = [
        symbol
        for symbol in non_hooked_symbol_names(definition=definition, main_module_name=main_module_name, non_hooked_only=False)
        if symbol != 'inj'
    ]

    sort_names_mangled = [mangle_even_more(n) for n in sort_names]
    symbol_names_mangled = [mangle_even_more(n) for n in symbol_names]

    output_text = coq_preamble \
        + inductive_sorts(sort_names_mangled) \
        + inductive_sorts_helpers(sort_names_mangled)\
        + inductive_symbols(symbol_names_mangled)\
        + eqdec_finite("Symbols", symbol_names_mangled)\
        + symbols_return_sorts("Symbols", symbol_names=symbol_names, definition=definition, main_module_name=main_module_name)\
        + symbols_arg_sorts("Symbols", symbol_names=symbol_names, definition=definition, main_module_name=main_module_name)\
        + "\n"

    with open(output_v_filename, mode="w") as fw:
        fw.write(output_text)
    

def main():
    parser = argparse.ArgumentParser(
                prog='koreimport',
                description='Generates a *.v file from a *.kore.')
    
    parser.add_argument('korefilename')
    parser.add_argument('--module-name', required=True)
    parser.add_argument('-o', '--output', required=True)

    args = parser.parse_args()
    generate(input_kore_filename=args.korefilename, main_module_name=args.module_name, output_v_filename=args.output)    
