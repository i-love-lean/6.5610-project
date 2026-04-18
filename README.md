# 6-5610-project

How to install Lurk:
1. `git clone https://github.com/lurk-lab/lurk.git`
2. `cd lurk`
3. `cargo install --path . --locked`

Lurk docs: https://docs.argument.xyz/

Lurk gotchas:

Q: Difference between `(cons 1 2)` and `(list 1 2)`? A: `(cons 1 2)` reduces to `(1 . 2)` and `(list 1 2)` reduces to `(1 2)` which is equivalent to `(1 . (2))`. Basically, `(cdr '(1 . 2))` returns `2` while `cdr '(1 2)` returns `(2)`.

