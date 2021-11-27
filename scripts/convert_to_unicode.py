from pathlib import Path
import re

def to_unicode(s: str):
	return bytes(s,'ascii').decode("unicode-escape")

def find_unicodes(f: Path):
	try:
		patt = re.compile(r'\\'+'u[a-f0-9]{4}')
		return f, set(patt.findall(f.open('r').read()))
	except UnicodeDecodeError:
		raise
if __name__ == '__main__':
	AML = Path.cwd()
	while AML.name != 'AML-Formalization':
		AML = AML.parent
	root = AML # / 'matching-logic' / 'src'
	replaces = []
	print('The following unicodes were found in the following .v files:')
	for f in root.glob('*/*/*.v'):
		res = find_unicodes(f)
		if len(res[1]) > 0:
			print(res[0].relative_to(AML))
			for i in res[1]:
				replaces.append((i,to_unicode(i)))
				print(f'\t{replaces[-1]}')
	print(f"{len(replaces)} codes were replaced in the .v files")
	replaces = set(replaces)
	for f in root.glob('*/*/*.v'):
		data = f.open('r').read()
		for esc, uni in replaces:
			data = data.replace(esc,uni)
		f.open("w",encoding='utf8').write(data)