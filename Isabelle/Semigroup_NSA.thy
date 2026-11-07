theory Semigroup_NSA
  imports
    "HOL-Analysis.Analysis"
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
begin

no_notation eqpoll (infixl \<open>\<approx>\<close> 50)

text \<open>
  A nonstandard proof, after Euler, that a one-parameter semigroup \<open>M\<close> that is continuous on
  \<open>[0, \<infinity>)\<close> is an exponential, \<open>M t = exp (t A)\<close>, in a finite-dimensional
  (Heine--Borel) Banach algebra.

  \<^enum> The difference quotients \<open>(M h - 1) / h\<close> are bounded for small \<open>h > 0\<close>
    (geometric sums; ordinary analysis).
  \<^enum> By transfer, \<open>(M \<epsilon> - 1) / \<epsilon>\<close> is finite for the infinitesimal
    \<open>\<epsilon> = 1 / \<omega>\<close>, so it has a standard part \<open>A\<close>.
  \<^enum> Each step of size \<open>\<epsilon>\<close> multiplies \<open>M s * exp (- s A)\<close> by a factor
    that differs from \<open>1\<close> by \<open>\<epsilon>\<close> times an infinitesimal. Over
    \<open>\<lfloor>t / \<epsilon>\<rfloor>\<close> steps the changes add up to an infinitesimal
    (a transferred telescoping estimate), so the product stays \<open>1\<close>.
\<close>

section \<open>Ordinary analysis: bounded difference quotients and telescoping\<close>

lemma floor_step:
  assumes "0 \<le> t" "0 < h"
  shows "t - h \<le> real (nat \<lfloor>t / h\<rfloor>) * h" "real (nat \<lfloor>t / h\<rfloor>) * h \<le> t"
  using floor_divide_lower[of h t] floor_divide_upper[of h t] assms
  by (simp_all add: algebra_simps)

lemma geometric_quotient_bound:
  fixes x :: "'a::real_normed_algebra_1"
  assumes near: "\<And>k. k < n \<Longrightarrow> norm (x ^ k - 1) \<le> 1 / 2"
  shows "norm (real n *\<^sub>R (x - 1)) \<le> 2 * norm (x ^ n - 1)"
proof -
  have "(x - 1) * (\<Sum>k<n. x ^ k) = x ^ n - 1"
    by (induction n) (simp_all add: algebra_simps)
  then have eq: "real n *\<^sub>R (x - 1) - (x ^ n - 1) = (x - 1) * (\<Sum>k<n. 1 - x ^ k)"
    by (simp add: sum_subtractf right_diff_distrib left_diff_distrib scaleR_conv_of_real
      mult_of_nat_commute)
  have "norm (real n *\<^sub>R (x - 1)) - norm (x ^ n - 1) \<le> norm (x - 1) * norm (\<Sum>k<n. 1 - x ^ k)"
    using norm_triangle_ineq2[of "real n *\<^sub>R (x - 1)" "x ^ n - 1"]
      norm_mult_ineq[of "x - 1" "\<Sum>k<n. 1 - x ^ k"]
    unfolding eq by linarith
  also have "\<dots> \<le> norm (x - 1) * (\<Sum>k<n. 1 / 2)"
    using near by (intro mult_left_mono order_trans[OF norm_sum sum_mono])
      (simp_all add: norm_minus_commute)
  finally show ?thesis
    by simp
qed

lemma bounded_quotients:
  fixes M :: "real \<Rightarrow> 'a::real_normed_algebra_1"
  assumes cont: "continuous (at 0 within {0..}) M" and M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
  shows "\<exists>\<delta>>0. \<forall>h. 0 < h \<longrightarrow> h \<le> \<delta> \<longrightarrow> norm ((1 / h) *\<^sub>R (M h - 1)) \<le> 1 / \<delta>"
proof -
  obtain r where "r > 0" and r: "\<And>s. 0 \<le> s \<Longrightarrow> s < r \<Longrightarrow> norm (M s - 1) < 1 / 2"
    using cont[unfolded continuous_within_eps_delta, rule_format, of "1 / 2"] M0
    by (auto simp: dist_norm)
  have "norm ((1 / h) *\<^sub>R (M h - 1)) \<le> 1 / (r / 4)" if "0 < h" "h \<le> r / 4" for h
  proof -
    define m where "m = nat \<lfloor>(r / 2) / h\<rfloor>"
    have m: "r / 2 - h \<le> real m * h" "real m * h \<le> r / 2"
      unfolding m_def using floor_step[of "r / 2" h] \<open>r > 0\<close> that by simp_all
    have pow: "M h ^ k = M (real k * h)" for k
    proof (induction k)
      case (Suc k)
      then show ?case
        using add[of "real k * h" h] \<open>0 < h\<close> by (simp add: power_Suc2 algebra_simps del: power_Suc)
    qed (simp add: M0)
    have "norm (real m *\<^sub>R (M h - 1)) \<le> 2 * norm (M h ^ m - 1)"
    proof (rule geometric_quotient_bound)
      fix k
      assume "k < m"
      then have "real k * h \<le> real m * h"
        using \<open>0 < h\<close> by (intro mult_right_mono) simp_all
      then have "real k * h < r"
        using m(2) \<open>r > 0\<close> by linarith
      then show "norm (M h ^ k - 1) \<le> 1 / 2"
        using r[of "real k * h"] \<open>0 < h\<close> by (simp add: pow)
    qed
    also have "\<dots> \<le> 1"
      using r[of "real m * h"] m(2) \<open>0 < h\<close> \<open>r > 0\<close> by (simp add: pow)
    finally have mn: "real m * norm (M h - 1) \<le> 1"
      by simp
    have "r / 4 \<le> real m * h"
      using m(1) that by linarith
    then have "norm (M h - 1) * (r / 4) \<le> (real m * norm (M h - 1)) * h"
      using mult_left_mono[of "r / 4" "real m * h" "norm (M h - 1)"] by (simp add: ac_simps)
    also have "\<dots> \<le> h"
      using mult_right_mono[OF mn, of h] \<open>0 < h\<close> by simp
    finally have "norm (M h - 1) * (r / 4) \<le> h" .
    then have "norm (M h - 1) / h \<le> 1 / (r / 4)"
      using that \<open>r > 0\<close> by (simp add: field_simps)
    then show ?thesis
      using that by (simp only: norm_scaleR) simp
  qed
  then show ?thesis
    using \<open>r > 0\<close> by (intro exI[of _ "r / 4"]) auto
qed

text \<open>Telescoping over \<open>\<lfloor>t / h\<rfloor>\<close> steps of size \<open>h\<close>.\<close>

lemma telescope_bound:
  fixes M E :: "real \<Rightarrow> 'a::real_normed_algebra_1"
  assumes M0: "M 0 = 1" and E0: "E 0 = 1"
    and Madd: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
    and Eadd: "\<And>s u. E (s + u) = E s * E u"
    and C: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (M s) \<le> C"
    and D: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (E s) \<le> D"
    and "0 \<le> t" "0 < h"
  shows "norm (M (real (nat \<lfloor>t / h\<rfloor>) * h) * E (real (nat \<lfloor>t / h\<rfloor>) * h) - 1)
    \<le> t * C * D * norm ((1 / h) *\<^sub>R (M h * E h - 1))"
proof -
  define K where "K = nat \<lfloor>t / h\<rfloor>"
  define F where "F j = M (real j * h) * E (real j * h)" for j
  have Kt: "real K * h \<le> t"
    unfolding K_def using floor_step \<open>0 \<le> t\<close> \<open>0 < h\<close> by blast
  have CD: "0 \<le> C" "0 \<le> D"
    using C[of 0] D[of 0] \<open>0 \<le> t\<close> by (auto intro: order_trans[OF norm_ge_zero])
  have step: "norm (F (Suc j) - F j) \<le> C * norm (M h * E h - 1) * D" if "j < K" for j
  proof -
    have "real j * h \<le> real K * h"
      using that \<open>0 < h\<close> by (intro mult_right_mono) simp_all
    then have "real j * h \<le> t"
      using Kt by linarith
    then have js: "real j * h \<in> {0..t}"
      using \<open>0 < h\<close> by simp
    have eq: "F (Suc j) - F j = M (real j * h) * (M h * E h - 1) * E (real j * h)"
      using Madd[of "real j * h" h] Eadd[of h "real j * h"] \<open>0 < h\<close>
      by (simp add: F_def algebra_simps)
    have "norm (M (real j * h) * (M h * E h - 1) * E (real j * h))
        \<le> norm (M (real j * h)) * norm (M h * E h - 1) * norm (E (real j * h))"
      by (rule order_trans[OF norm_mult_ineq mult_right_mono[OF norm_mult_ineq norm_ge_zero]])
    also have "\<dots> \<le> C * norm (M h * E h - 1) * D"
      using C[OF js] D[OF js] CD by (intro mult_mono mult_right_mono) simp_all
    finally show ?thesis
      unfolding eq .
  qed
  have "norm (F K - F 0) = norm (\<Sum>j<K. F (Suc j) - F j)"
    by (simp only: sum_lessThan_telescope)
  also have "\<dots> \<le> (\<Sum>j<K. C * norm (M h * E h - 1) * D)"
    by (rule order_trans[OF norm_sum sum_mono]) (simp add: step)
  also have "\<dots> = real K * h * (C * D * norm ((1 / h) *\<^sub>R (M h * E h - 1)))"
    using \<open>0 < h\<close> by (simp add: abs_of_pos)
  also have "\<dots> \<le> t * (C * D * norm ((1 / h) *\<^sub>R (M h * E h - 1)))"
    using Kt CD by (intro mult_right_mono) simp_all
  finally show ?thesis
    by (simp add: F_def K_def M0 E0 mult.assoc)
qed

section \<open>Nonstandard analysis: standard parts of finite vectors\<close>

text \<open>
  The library provides standard parts of finite hyperreals. In a Heine--Borel space, every
  finite vector also has a standard part: the ultrafilter image of its representing sequence
  clusters at some point of a closed ball, and an ultrafilter that clusters at a point
  converges to it.
\<close>

lemma HFinite_approx_star_of:
  fixes x :: "'a::{real_normed_vector, heine_borel} star"
  assumes "x \<in> HFinite"
  shows "\<exists>a. x \<approx> star_of a"
proof -
  obtain X where x: "x = star_n X" by (cases x)
  then obtain u where "eventually (\<lambda>n. norm (X n) < u) \<U>"
    using assms HFinite_FreeUltrafilterNat_iff by blast
  then have "eventually (\<lambda>y. y \<in> cball 0 u) (filtermap X \<U>)"
    unfolding eventually_filtermap by (rule eventually_mono) simp
  moreover have "filtermap X \<U> \<noteq> bot"
    by (simp add: filtermap_bot_iff FreeUltrafilterNat.proper)
  ultimately obtain a where a: "inf (nhds a) (filtermap X \<U>) \<noteq> bot"
    using compact_filter[THEN iffD1, OF compact_cball[of 0 u]] by blast
  have lim: "eventually (\<lambda>n. X n \<in> S) \<U>" if "open S" "a \<in> S" for S
  proof (rule ccontr)
    assume "\<not> eventually (\<lambda>n. X n \<in> S) \<U>"
    then have "eventually (\<lambda>y. y \<notin> S) (filtermap X \<U>)"
      by (simp add: FreeUltrafilterNat.eventually_not_iff eventually_filtermap)
    then have "eventually (\<lambda>y. False) (inf (nhds a) (filtermap X \<U>))"
      using eventually_nhds_in_open[OF that] unfolding eventually_inf by blast
    then show False
      using a by (simp add: eventually_False)
  qed
  have "x \<approx> star_of a"
    unfolding x star_of_def approx_FreeUltrafilterNat_iff
    using lim[OF open_ball, of a] by (simp add: dist_norm norm_minus_commute)
  then show ?thesis ..
qed

section \<open>The semigroup theorem\<close>

theorem semigroup_eq_exp:
  fixes M :: "real \<Rightarrow> 'a::{real_normed_algebra_1, banach, heine_borel}"
  assumes cont: "continuous_on {0..} M" and M0: "M 0 = 1"
    and add: "\<And>s t. 0 \<le> s \<Longrightarrow> 0 \<le> t \<Longrightarrow> M (s + t) = M s * M t"
  shows "\<exists>A. \<forall>t\<ge>0. M t = exp (t *\<^sub>R A)"
proof -
  define Q where "Q = (\<lambda>h. (1 / h) *\<^sub>R (M h - 1))"
  have "continuous (at 0 within {0..}) M"
    using cont by (simp add: continuous_on_eq_continuous_within)
  then obtain \<delta> where "\<delta> > 0" and "\<forall>h. 0 < h \<longrightarrow> h \<le> \<delta> \<longrightarrow> norm (Q h) \<le> 1 / \<delta>"
    using bounded_quotients[of M, OF _ M0 add] unfolding Q_def by blast

  txt \<open>By transfer, \<open>Q \<epsilon>\<close> is finite, so it has a standard part \<open>A\<close>.\<close>
  then have "\<forall>h. 0 < h \<longrightarrow> h \<le> star_of \<delta> \<longrightarrow> hnorm (( *f* Q) h) \<le> star_of (1 / \<delta>)"
    by transfer
  moreover have "\<epsilon> \<le> star_of \<delta>"
    using Infinitesimal_less_SReal[OF SReal_hypreal_of_real Infinitesimal_epsilon] \<open>\<delta> > 0\<close>
    by (simp add: less_imp_le)
  ultimately have "hnorm (( *f* Q) \<epsilon>) < star_of (1 / \<delta> + 1)"
    using epsilon_gt_zero by fastforce
  then have "( *f* Q) \<epsilon> \<in> HFinite"
    unfolding HFinite_def by (blast intro: SReal_hypreal_of_real)
  then obtain A where A: "( *f* Q) \<epsilon> \<approx> star_of A"
    using HFinite_approx_star_of by blast

  txt \<open>Euler's step: \<open>F s = M s * exp (- s A)\<close> stays \<open>1\<close>.\<close>
  have "M t = exp (t *\<^sub>R A)" if "0 < t" for t
  proof -
    define E where "E = (\<lambda>s. exp (s *\<^sub>R - A))"
    define DE where "DE = (\<lambda>h. (1 / h) *\<^sub>R (E h - 1))"
    define F where "F = (\<lambda>s. M s * E s)"
    define G where "G = (\<lambda>h. (1 / h) *\<^sub>R (F h - 1))"
    define K where "K = (\<lambda>h. real (nat \<lfloor>t / h\<rfloor>) * h)"
    have E0: "E 0 = 1"
      by (simp add: E_def)
    have Eadd: "E (s + u) = E s * E u" for s u
      unfolding E_def scaleR_add_left by (rule exp_add_commuting) (simp add: algebra_simps)
    have Ederiv: "(E has_vector_derivative E s * - A) (at s)" for s
      using exp_scaleR_has_vector_derivative_right[of "- A" s UNIV] by (simp add: E_def)
    have Econt: "isCont E s" for s
      using has_vector_derivative_continuous[OF Ederiv[of s]] .
    obtain C where C: "\<And>s. s \<in> {0..t} \<Longrightarrow> norm (M s) \<le> C"
    proof -
      have "bounded (M ` {0..t})"
        by (intro compact_imp_bounded compact_continuous_image continuous_on_subset[OF cont]) auto
      then obtain a where "\<forall>x \<in> M ` {0..t}. norm x \<le> a"
        unfolding bounded_iff ..
      then show ?thesis
        by (intro that[of a]) auto
    qed
    have D: "norm (E s) \<le> exp (t * norm A)" if "s \<in> {0..t}" for s
    proof -
      have "s * norm A \<le> t * norm A"
        using that by (intro mult_right_mono) simp_all
      then show ?thesis
        using that by (auto simp: E_def intro!: order_trans[OF norm_exp])
    qed

    txt \<open>One step of size \<open>\<epsilon>\<close> changes \<open>F\<close> by \<open>\<epsilon>\<close> times an infinitesimal.\<close>
    have "(DE \<longlongrightarrow> - A) (at 0)"
      using Ederiv[of 0] unfolding has_vector_derivative_within_1D
      by (simp add: DE_def E0 inverse_eq_divide)
    then have DE: "( *f* DE) \<epsilon> \<approx> star_of (- A)"
      by (auto dest!: LIM_NSLIM simp: NSLIM_def)
    have E_eps: "( *f* E) \<epsilon> \<approx> star_of 1"
      using isNSContD[OF isCont_isNSCont[OF Econt[of 0]], of \<epsilon>] E0 by simp
    have "G = (\<lambda>h. Q h * E h + DE h)"
      by (simp add: fun_eq_iff G_def F_def Q_def DE_def algebra_simps)
    then have "( *f* G) \<epsilon> = ( *f* Q) \<epsilon> * ( *f* E) \<epsilon> + ( *f* DE) \<epsilon>"
      by simp
    also have "\<dots> \<approx> star_of A * star_of 1 + star_of (- A)"
      using A E_eps DE by (intro approx_add approx_mult_star_of)
    finally have G0: "( *f* G) \<epsilon> \<in> Infinitesimal"
      by (simp add: mem_infmal_iff)

    txt \<open>Over \<open>\<lfloor>t / \<epsilon>\<rfloor>\<close> steps these changes add up to an infinitesimal.\<close>
    have "\<forall>h>0. norm (F (K h) - 1) \<le> t * C * exp (t * norm A) * norm (G h)
        \<and> t - h \<le> K h \<and> K h \<le> t"
      using telescope_bound[of M E, OF M0 E0 add Eadd C D] floor_step[of t] \<open>0 < t\<close>
      by (simp add: F_def G_def K_def)
    then have "\<forall>h>0. hnorm (( *f* F) (( *f* K) h) - 1)
          \<le> star_of (t * C * exp (t * norm A)) * hnorm (( *f* G) h)
        \<and> star_of t - h \<le> ( *f* K) h \<and> ( *f* K) h \<le> star_of t"
      by transfer
    then have FK: "hnorm (( *f* F) (( *f* K) \<epsilon>) - 1)
          \<le> star_of (t * C * exp (t * norm A)) * hnorm (( *f* G) \<epsilon>)"
        and "star_of t - \<epsilon> \<le> ( *f* K) \<epsilon>" "( *f* K) \<epsilon> \<le> star_of t"
      using epsilon_gt_zero by blast+
    then have "( *f* K) \<epsilon> \<approx> star_of t"
      by (metis approx_diff approx_le_bound approx_reorient diff_0_right epsilon_approx_zero
        star_of_approx_iff)
    then have "( *f* F) (( *f* K) \<epsilon>) \<approx> star_of (F t)"
      using continuous_on_interior[OF cont] Econt \<open>0 < t\<close>
      by (intro isNSContD isCont_isNSCont) (simp_all add: F_def)
    moreover have "( *f* F) (( *f* K) \<epsilon>) \<approx> 1"
      using FK G0 by (meson Infinitesimal_hnorm_iff Infinitesimal_star_of_mult2 approx_def
        hnorm_le_Infinitesimal)
    ultimately have "M t * exp (t *\<^sub>R - A) = 1"
      using approx_trans3 star_of_approx_iff star_of_one by (metis F_def E_def)
    then show ?thesis
      by (metis add.inverse_inverse exp_minus_inverse mult.assoc mult_minus1_right
        scaleR_minus_right)
  qed
  then show ?thesis
    using M0 by (metis exp_zero less_eq_real_def scale_zero_left)
qed

end
