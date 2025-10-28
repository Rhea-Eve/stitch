import json
import re
import sys

'''
Input → .v (Coq file)

Output → .json (list of Lisp-like λ-terms)
'''

def coq_to_lisp(coq_code: str):
    # Match simple definitions like: Definition f (x : nat) := S x.
    pattern = r"Definition\s+(\w+)\s*\((\w+)\s*:\s*[\w\s]+\)\s*:=\s*(.+?)\."
    matches = re.findall(pattern, coq_code, flags=re.S)
    lisp_terms = []
    for name, arg, body in matches:
        body = body.strip().replace("\n", " ")
        # convert Coq-style function application to Lisp
        body = re.sub(r"(\w+)\s+(\w+)", r"(\1 \2)", body)
        lisp = f"(lam ({arg} {body}))"
        lisp_terms.append(lisp)
    return lisp_terms

if __name__ == "__main__":
    infile = sys.argv[1]
    outfile = sys.argv[2]
    with open(infile) as f:
        coq_code = f.read()
    terms = coq_to_lisp(coq_code)
    with open(outfile, "w") as f:
        json.dump(terms, f, indent=4)
    print(f"Wrote {len(terms)} term(s) to {outfile}")
