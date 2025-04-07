
theory Hadamard_Verification
  imports Complex_Main "HOL-Library.Matrix"
begin

definition H :: "complex Matrix.mat"
  where "H = (λ(i,j). (1 / sqrt 2) * (if i = 0 ∧ j = 0 then 1
                                else if i = 0 ∧ j = 1 then 1
                                else if i = 1 ∧ j = 0 then 1
                                else if i = 1 ∧ j = 1 then -1
                                else 0))"

definition conj_transpose :: "complex Matrix.mat ⇒ complex Matrix.mat"
  where "conj_transpose A = (λ(i,j). cnj (A j i))"

definition I2 :: "complex Matrix.mat"
  where "I2 = (λ(i,j). if i = j ∧ i < 2 ∧ j < 2 then 1 else 0)"

lemma hadamard_unitary: "Matrix.mat_mult (conj_transpose H) H = I2"
proof -
  have "∀i j < 2. Matrix.mat_mult (conj_transpose H) H i j =
       (if i = j then 1 else 0)"
  proof (intro allI impI)
    fix i j assume "i < 2" and "j < 2"
    let ?s = "∑k<2. cnj (H k i) * H k j"
    show "Matrix.mat_mult (conj_transpose H) H i j = (if i = j then 1 else 0)"
      unfolding conj_transpose_def H_def Matrix.mat_mult_def I2_def
      using `i < 2` `j < 2`
      by (cases i; cases j; simp add: complex_of_real_def)
  qed
  then show ?thesis
    by (auto simp add: fun_eq_iff I2_def Matrix.mat_mult_def)
qed
