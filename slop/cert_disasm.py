#!/usr/bin/env python3
"""Disassembler for cert_*.lurk dumps.

Usage:  cert_disasm.py <file>

Parses the term-table, eval-table, rule-table out of a generated certificate
dump and prints them as readable bytecode.
"""

import re
import sys

# ---------- Lurk reader (just enough for our cells) ----------

TOKEN = re.compile(r"\(|\)|'|;[^\n]*\n|\s+|[^()\s'`,]+")

def tokenize(s):
    out = []
    i = 0
    while i < len(s):
        m = TOKEN.match(s, i)
        if not m:
            raise ValueError(f"bad char at {i}: {s[i:i+30]!r}")
        tok = m.group()
        i = m.end()
        if tok.startswith(";") or tok.isspace():
            continue
        out.append(tok)
    return out

def parse(tokens, pos):
    """Returns (sexp, new_pos)."""
    tok = tokens[pos]
    pos += 1
    if tok == "'":
        v, pos = parse(tokens, pos)
        return ("quote", v), pos
    if tok == "(":
        items = []
        while tokens[pos] != ")":
            v, pos = parse(tokens, pos)
            items.append(v)
        return items, pos + 1  # skip ")"
    if tok == ")":
        raise ValueError("unexpected )")
    return tok, pos  # leaf

def parse_one(s):
    toks = tokenize(s)
    v, pos = parse(toks, 0)
    return v

# ---------- balanced-tree decoder (Lurk side: tree-lookup) ----------

def tree_to_list(tree, size):
    """Mirror the verifier's tree-lookup: take a `(cons L R)` tree built by
    Lean's `buildBalanced` for `size` items and flatten back to a list."""
    if size == 1:
        return [tree]
    half = size // 2
    if not (isinstance(tree, list) and len(tree) == 2 and tree[0] == "cons"):
        raise ValueError(f"expected (cons L R), got {tree}")
    left, right = tree[1], tree[2] if False else None  # placeholder

# Cons sexps from our parser come in as ['cons', L, R].
def tree_to_list2(tree, size):
    if size == 1:
        return [tree]
    half = size // 2
    assert isinstance(tree, list) and len(tree) == 3 and tree[0] == "cons", \
        f"want (cons L R), got {tree}"
    return tree_to_list2(tree[1], half) + tree_to_list2(tree[2], size - half)

# ---------- mnemonics ----------

TAG_NAMES = {
    0: "VAR", 1: "LAM", 2: "APP", 3: "TYP", 4: "FN",
    5: "PROD", 6: "PMK", 7: "PRC",
    8: "SUM", 9: "INL", 10: "INR", 11: "SRC",
    12: "EQ", 13: "REFL", 14: "ERC",
    15: "NAT", 16: "ZERO", 17: "SUCC", 18: "NRC",
    19: "UNIT", 20: "INTRO", 21: "FLS", 22: "FRC",
    23: "OPAQUE",
}
RULE_NAMES = {
    0: "ID", 1: "CONG-LAM", 2: "CONG-FN", 3: "CONG-APP",
    4: "CONG-PROD", 5: "CONG-SUM", 6: "CONG-EQ",
    7: "BETA",
    8: "IOTA-PROD", 9: "IOTA-SUM-L", 10: "IOTA-SUM-R",
    11: "IOTA-EQ", 12: "IOTA-NAT-Z", 13: "IOTA-NAT-S",
}

def parse_n(s):
    """Parse a Lurk numeric token: '5n' (field) or '5' (u64)."""
    if s.endswith("n"):
        return int(s[:-1])
    return int(s)

# ---------- disassembly ----------

def disasm_node(idx, cell):
    """cell = ['quote', [tag-tok, args...]] from the term-table."""
    assert cell[0] == "quote"
    inner = cell[1]
    tag = parse_n(inner[0])
    name = TAG_NAMES.get(tag, f"#{tag}")
    rest = inner[1:]
    if tag in (0, 3, 23):                     # var / typ / opaque — payload only
        body = f"{rest[0]}"
    elif tag in (1, 2, 4, 5, 8, 12):          # lam/app/fn/prod/sum/eq — child idxs
        body = " ".join(f"#{c}" for c in rest)
    else:                                     # bare constants
        body = ""
    return f"[{idx:4}] {name:5} {body}".rstrip()

def disasm_rule(idx, cell):
    """cell = ['quote', [rule-tok, output-tok, witnesses...]]"""
    assert cell[0] == "quote"
    inner = cell[1]
    rule = parse_n(inner[0])
    rname = RULE_NAMES.get(rule, f"R{rule}")
    out = inner[1]
    ws = inner[2:]
    head = f"  {rname:9} #{idx:4} -> #{out}"
    if not ws:
        return head
    return head + "   witnesses: " + " ".join(f"#{w}" for w in ws)

def main():
    if len(sys.argv) != 2:
        print("usage: cert_disasm.py <file.lurk>", file=sys.stderr)
        sys.exit(1)
    src = open(sys.argv[1]).read()

    def find(name):
        m = re.search(rf"!\(def {name}\s+(.+?)\)\s*\n\s*(?=!\(|;|\Z)", src, re.DOTALL)
        if not m:
            raise ValueError(f"couldn't find !(def {name} ...)")
        return m.group(1).strip()

    n = int(find("N"))
    term_tree = parse_one(find("term-table"))
    eval_tree = parse_one(find("eval-table"))
    rule_tree = parse_one(find("rule-table"))

    terms = tree_to_list2(term_tree, n)
    evals = tree_to_list2(eval_tree, n)
    rules = tree_to_list2(rule_tree, n)

    print(f";; {sys.argv[1]}: {n} nodes\n")
    for i in range(n):
        node_str = disasm_node(i, terms[i])
        rule_str = disasm_rule(i, rules[i])
        print(f"{node_str:34}{rule_str}")

if __name__ == "__main__":
    main()
