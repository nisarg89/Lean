import FairDivision.Statements.Existence
import FairDivision.BF.MainTheorems

/-!
# Stable existence-only solution names

These aliases preserve the independently frozen Comparator propositions.
They import the actual BF proofs, never the isolated Challenge statements.
-/

set_option autoImplicit false

namespace FairDivision.BF

theorem exists_balanced_ef11_identical_prime_power : Statements.identicalPrimePower:=by
  intro n m hn hPrimePower v
  exact MainTheorems.identical_prime_power_ef11 n m hPrimePower v

theorem exists_balanced_ef11_identical : Statements.identicalAllN:=by
  intro n m hn v
  exact MainTheorems.identical_ef11 n m hn v

theorem exists_balanced_ef11_heterogeneous_prime_power : Statements.heterogeneousPrimePower:=by
  intro n m hn hPrimePower v
  exact MainTheorems.heterogeneous_prime_power_ef11 n m hPrimePower v

end FairDivision.BF
