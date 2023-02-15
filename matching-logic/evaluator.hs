import Test

toInt :: Nat -> Integer
toInt O = 0
toInt (S x) = 1 + toInt x

instance Show Nat where
  show x = show $ toInt x

propositional_proof_sizes = [
  ("Hilbert proof", proof_prop_low),
  ("Low-level proof mode proof", proof_prop_pm1),
  ("High-level proof mode proof", proof_prop_pm2)
  ]

rewrite_proof_sizes = [
  ("Framing-based proof",proof_rew_low),
  ("Congruence lemma-based proof", proof_rew_pm1),
  ("mlRewrite-based proof", proof_rew_pm2),
  ("mlRewrite-based proof opposite", proof_rew_pm3)
  ]

fol_proof_sizes = [
  ("Hilbert proof", proof_fol_low),
  ("Proof using only FOL proof mode", proof_fol_pm1),
  ("Proof mode proof", proof_fol_pm2)
  ]

revert_proof_sizes = [
  ("Derived revert",proof_derived_rev_small),
  ("Induction-based revert",proof_pm_rev_small),
  ("Derived revert with hypotheses",proof_derived_rev_big),
  ("Induction-based revert with hypotheses",proof_pm_rev_big)
  ]

complex_proof_sizes = [
  ("Hilbert proof", proof_complex_low),
  ("Proof mode proof", proof_complex_pm)
  ]

main :: IO ()
main = do
  putStrLn (show  propositional_proof_sizes)
  putStrLn (show rewrite_proof_sizes)
  putStrLn (show fol_proof_sizes)
  putStrLn (show revert_proof_sizes)
  putStrLn (show complex_proof_sizes)