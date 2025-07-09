module TREE
  imports INT
  imports LIST
  imports BOOL

  // === Sorts ===
  syntax Tree ::= "Empty"
                | "Node" "(" Int "," Int "," Tree "," Tree ")" // Node(Value, Height, Left, Right)

  syntax IntList ::= List{Int, ","}         // For traversals

  // === Constructors ===
  syntax Tree ::= node(Int, Tree, Tree) [function]
  rule node(V, L, R) => Node(V, 1 +Int maxInt(height(L), height(R)), L, R)

  // === Height ===
  syntax Int ::= height(Tree) [function]
  rule height(Empty) => 0
  rule height(Node(_, H, _, _)) => H

  // === Balance Factor ===
  syntax Int ::= balanceFactor(Tree) [function]
  rule balanceFactor(Empty) => 0
  rule balanceFactor(Node(_, _, L, R)) => height(L) -Int height(R)

  // === Rotations ===

  syntax Tree ::= rotateLeft(Tree) [function]
  rule rotateLeft(Node(X, _, A, Node(Y, _, B, C))) =>
    node(Y, node(X, A, B), C)

  syntax Tree ::= rotateRight(Tree) [function]
  rule rotateRight(Node(Y, _, Node(X, _, A, B), C)) =>
    node(X, A, node(Y, B, C))

  syntax Tree ::= rotateLeftRight(Tree) [function]
  rule rotateLeftRight(T) => rotateRight(node(value(T), rotateLeft(leftT(T)), rightT(T)))
    requires isNode(leftT(T))

  syntax Tree ::= rotateRightLeft(Tree) [function]
  rule rotateRightLeft(T) => rotateLeft(node(value(T), leftT(T), rotateRight(rightT(T))))
    requires isNode(rightT(T))

  syntax Bool ::= isNode(Tree) [function]
  rule isNode(Node(_, _, _, _)) => true
  rule isNode(_) => false [owise]

  syntax Tree ::= leftT(Tree) [function]
  rule leftT(Node(_, _, L, _)) => L
  rule leftT(_) => Empty [owise]

  syntax Tree ::= rightT(Tree) [function]
  rule rightT(Node(_, _, _, R)) => R
  rule rightT(_) => Empty [owise]

  syntax Int ::= value(Tree) [function]
  rule value(Node(V, _, _, _)) => V
  rule value(_) => 0 [owise]

  // === Insertion with balancing ===
  syntax Tree ::= insert(Tree, Int) [function]
  rule insert(Empty, V) => node(V, Empty, Empty)

  //rule insert(Node(X, _, L, R), V) =>
  //  balance(
  //    if V <Int X 
  //      then node(X, insert(L, V), R)
  //      else node(X, L, insert(R, V))
  //  )
  rule insert(Node(X, _, L, R), V) => balance(node(X, insert(L, V), R)) requires V <Int X
  rule insert(Node(X, _, L, R), V) => balance(node(X, L, insert(R, V))) requires V >=Int X


  // === Balance ===
  syntax Tree ::= balance(Tree) [function]
  rule balance(T) => rotateRight(T) requires (balanceFactor(T) >Int 1) andBool balanceFactor(leftT(T)) >=Int 0

  rule balance(T) => rotateLeftRight(T) requires balanceFactor(T) >Int 1 andBool balanceFactor(leftT(T)) <Int 0

  rule balance(T) => rotateLeft(T) requires balanceFactor(T) <Int -1 andBool balanceFactor(rightT(T)) <=Int 0

  rule balance(T) => rotateRightLeft(T) requires balanceFactor(T) <Int -1 andBool balanceFactor(rightT(T)) >Int 0

  rule balance(T) => T requires notBool (
                                  (balanceFactor(T) >Int 1 andBool balanceFactor(leftT(T)) >=Int 0)
                                  orBool
                                  (balanceFactor(T) >Int 1 andBool balanceFactor(leftT(T)) <Int 0)
                                  orBool
                                  (balanceFactor(T) <Int -1 andBool balanceFactor(rightT(T)) <=Int 0)
                                  orBool
                                  (balanceFactor(T) <Int -1 andBool balanceFactor(rightT(T)) >Int 0)
                                )

  // === Traversal (in-order) ===
  syntax List ::= inorder(Tree) [function]
  rule inorder(Empty) => .List
  rule inorder(Node(V, _, L, R)) => inorder(L) ListItem(V) inorder(R)

endmodule

