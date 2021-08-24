$[ mm/matching-logic.mm $]
$v var_x var_y $.
$d var_x var_y $.
var-x-is-element-var $f #ElementVariable var_x $.
var-y-is-element-var $f #ElementVariable var_y $.
the-proof-1 $p |- ( \exists var_x var_x )  $= var-x-is-element-var proof-rule-existence  $.
the-proof-2 $p |- ( \imp ( \exists var_x var_x ) ( \imp ( \exists var_y var_y ) ( \exists var_x var_x ) ) )  $= 
  var-x-is-element-var element-var-is-var var-is-pattern var-x-is-element-var exists-is-pattern
  var-y-is-element-var element-var-is-var var-is-pattern var-y-is-element-var exists-is-pattern
  proof-rule-prop-1  $.
