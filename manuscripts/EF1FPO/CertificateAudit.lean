import EF1FPO.Certificate

set_option autoImplicit false

namespace EF1FPO

example : BitPolynomial encodeInstance (fun I bits =>
    ∃ A : I.Allocation, I.IsEF1 A ∧ I.IsFPO A ∧ bits = encodeAllocation A) := ef1_fpo_polynomial

end EF1FPO

#print axioms EF1FPO.ef1_fpo_polynomial
