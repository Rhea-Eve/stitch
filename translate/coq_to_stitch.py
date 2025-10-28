import json
import sys

# This printer takes a restricted AST and prints Stitch-style Lisp.
def to_lisp(node):
    tag = node["tag"]

    if tag == "Var":
        return node["name"]

    if tag == "Const":
        return node["name"]

    if tag == "Lam":
        # Lam {name, body}
        return f"(lam ({node['name']} {to_lisp(node['body'])}))"

    if tag == "App":
        # App {fn, arg}
        fn_s = to_lisp(node["fn"])
        arg_s = to_lisp(node["arg"])
        return f"({fn_s} {arg_s})"

    if tag == "Pair":
        # program+proof pairing, e.g. (exist value proof)
        return f"(exist {to_lisp(node['val'])} {to_lisp(node['proof'])})"

    # add more cases as needed (If, And, Or, etc.)
    if tag == "If":
        return f"(if {to_lisp(node['cond'])} {to_lisp(node['then'])} {to_lisp(node['else'])})"

    if tag == "And":
        return f"(and {to_lisp(node['left'])} {to_lisp(node['right'])})"

    if tag == "EqRefl":
        return "eq_refl"

    return "UNSUPPORTED"

def main():
    infile = sys.argv[1]
    outfile = sys.argv[2]

    # We'll assume infile is a JSON array of ASTs, each entry one Coq def
    with open(infile) as f:
        asts = json.load(f)

    lisp_terms = []
    for ast in asts:
        lisp_terms.append(to_lisp(ast))

    with open(outfile, "w") as f:
        json.dump(lisp_terms, f, indent=4)

    print(f"Wrote {len(lisp_terms)} term(s) to {outfile}")

if __name__ == "__main__":
    main()
