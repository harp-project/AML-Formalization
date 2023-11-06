import argparse
import typing as T


import pyk.kore.parser as KoreParser
import pyk.kore.syntax as Kore

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


def sort_decls(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.SortDecl]:
    return [s for s in sentences(definition, main_module_name) if is_sort_decl(s)] #type: ignore

def non_hooked_sort_names(definition: Kore.Definition, main_module_name: str) -> T.Set[str]:
    sd = sort_decls(definition=definition, main_module_name=main_module_name)
    return {s.name for s in sd if not s.hooked}



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

def inductive_sorts(sort_names: T.List[str]) -> str:
    inductive_definition = f'''
    Inductive Sort :=
    {" ".join([f'| {s}' for s in sort_names])}
    .
    '''
    return inductive_definition

def inductive_sorts_helpers(sort_names: T.List[str]) -> str:
    helpers = '''
    #[global]
    Instance Sort_eqdec: EqDecision Sort.
    Proof.
        solve_decision.
    Defined.

    #[global]
    Program Instance Sort_finite: Finite Sort := {|
        enum := [
    '''
    
    helpers += ('; '.join(sort_names)) + '''];
    |}.
    Next Obligation.
        compute_done.
    Qed.
    Next Obligation.
        destruct x; compute_done.
    Qed.

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


def generate(input_kore_filename: str, main_module_name: str, output_v_filename: str):
    print(f'{input_kore_filename} > {output_v_filename}')
    parser = KoreParser.KoreParser(open(input_kore_filename).read())
    definition = parser.definition()
    sort_names: T.List[str] = list(non_hooked_sort_names(definition=definition, main_module_name=main_module_name))

    output_text = coq_preamble + inductive_sorts(sort_names) + inductive_sorts_helpers(sort_names)
    with open(output_v_filename, mode="w") as fw:
        fw.write(output_text)
    #print(output_text)
    

def main():
    print("Hello, world")

    parser = argparse.ArgumentParser(
                prog='koreimport',
                description='Generates a *.v file from a *.kore.')
    
    parser.add_argument('korefilename')
    parser.add_argument('--module-name', required=True)
    parser.add_argument('-o', '--output', required=True)

    args = parser.parse_args()
    generate(input_kore_filename=args.korefilename, main_module_name=args.module_name, output_v_filename=args.output)    
