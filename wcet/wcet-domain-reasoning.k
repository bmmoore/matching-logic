require "lib/naive-domain-reasoning.k"
require "wcet.k"

module WCET-DOMAIN-REASONING
  imports NAIVE-DOMAIN-REASONING
  imports WCET

/*
  rule manual('_impliesBag_) => .Set
  rule manual('_assertsBag_) => SetItem(T)
*/

  rule (<T>... <k> K </k> ...</T>) assertsBag (<T>... <k> K2 </k> ...</T>) => K impliesK K2

  rule (I +Int I2:#Int) +Int I3:#Int => I +Int (I2 +Int I3) when isSymbolicInt(I)
  rule I:Int |Int 0 => I

  syntax Int ::= Int "cdivInt" Int [function]
  syntax priorities '_cdivInt_ > '_+Int_

  rule I:Int cdivInt I2:Int => 0 -Int ((0 -Int I) divInt I2)

endmodule
