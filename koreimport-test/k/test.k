module TEST

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

endmodule
