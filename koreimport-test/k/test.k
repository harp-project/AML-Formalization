module TEST

  imports private BASIC-K

  syntax Color ::= Yellow() | Blue()
  syntax Fruit ::= Banana() | Blueberry()
  syntax Color ::= colorOf(Fruit) [function]

  syntax Taste ::= Good() | Bad()
                 | tasteOf(Fruit) [function]

  rule colorOf(Banana()) => Yellow()
  rule colorOf(Blueberry()) => Blue()

  rule tasteOf(Banana()) => Bad() [simplification]
  rule tasteOf(Blueberry()) => Good()
  rule tasteOf(Blueberry()) => Bad()

  syntax MyBool ::= "myNotBool" KItem "alma" KItem "cica"       [function, total]
                  | "myTrue"
                  | "myFalse"

  rule myNotBool myTrue alma myTrue cica => myFalse
  rule myNotBool _ alma _ cica => myTrue

endmodule
