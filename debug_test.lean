-- Quick test to understand Id monad
#check Id
#check Id.run
#check (5 : Id Nat)
#eval (5 : Id Nat).run