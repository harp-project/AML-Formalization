import argparse

import pyk.kore.parser as KoreParser
import pyk.kore.syntax as Kore


def generate(input_kore_filename: str, output_v_filename: str):
        print(f'{input_kore_filename} > {output_v_filename}')

def main():
    print("Hello, world")

    parser = argparse.ArgumentParser(
                prog='koreimport',
                description='Generates a *.v file from a *.kore.')
    
    parser.add_argument('korefilename')
    parser.add_argument('-o', '--output')

    args = parser.parse_args()
    generate(input_kore_filename=args.korefilename, output_v_filename=args.output)    
