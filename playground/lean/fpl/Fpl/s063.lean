/-! # The Applicative Contract
1. Identity: `pure id <*> v = v`
2. Function Composition: `pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`
3. Sequencing pure operations should be a no-op:
  `pure f <*> pure x = pure (f x)`
4. The ordering of pure operations doesn't matter:
  `u <*> pure x = pure (λ f => f x) <*> u`
-/
