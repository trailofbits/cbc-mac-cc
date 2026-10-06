import CBCMAC

/-!
# Axioms of CBC-MAC

The CBC construction, CR18 Theorem 6.1, the AES-256 instantiation and the upstream candidates
they use depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Upstream candidates: a program attached to a function.
#print axioms SystemAlgebra.Program.answer_of_exchanges
#print axioms SystemAlgebra.Program.inline_function
#print axioms SystemAlgebra.Program.trim_apply_ofProgramOn_function

-- Upstream candidates: loops against a function.
#print axioms SystemAlgebra.DSL.exchangesOf_foldTranscript
#print axioms SystemAlgebra.DSL.foldr_call_foldTranscript

-- Upstream candidates: sampling, filters and programs on functions, and the query filter.
#print axioms SystemAlgebra.Interface.Resource.sample_fTransform
#print axioms SystemAlgebra.Interface.Resource.smul_sample
#print axioms SystemAlgebra.Interface.filter_smul_ofFunction
#print axioms SystemAlgebra.Interface.Resource.ofFunction_eq_ofDeterministic
#print axioms SystemAlgebra.Interface.ofDDC_ofProgramOn_smul_ofFunction
#print axioms SystemAlgebra.Interface.queryFilter

-- The CBC construction.
#print axioms CBCMAC.cbcFunction
#print axioms CBCMAC.cbc
#print axioms CBCMAC.cbc.exact
#print axioms CBCMAC.θ
#print axioms CBCMAC.cbc_answer
#print axioms CBCMAC.cbc_smul_ofFunction
#print axioms CBCMAC.theta_cbc_eq

-- CR18 Theorem 6.1.
#print axioms CBCMAC.Collisions.mass_cbcFunction_outputs_and_not_cbcBad_eq
#print axioms CBCMAC.Collisions.mass_cbcBad_le
#print axioms CBCMAC.URF_eq
#print axioms CBCMAC.cbc_game_equiv
#print axioms CBCMAC.cbcGame_blind_bound
#print axioms CBCMAC.cbc_randomness_expander

-- AES-256 CBC-MAC.
#print axioms AESCBC.aes256
#print axioms AESCBC.blockForm_prefixFree
#print axioms AESCBC.aes256_cbc_prf
