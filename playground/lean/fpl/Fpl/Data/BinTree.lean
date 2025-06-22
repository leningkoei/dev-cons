inductive BinTree (α : Type) where
| leaf : BinTree α
| branch : BinTree α → α → BinTree α → BinTree α

def BinTree.mirror
: BinTree α → BinTree α
| .leaf => .leaf
| .branch l x r => .branch r.mirror x l.mirror
