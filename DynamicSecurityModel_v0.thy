theory DynamicSecurityModel_v0
imports Main
begin
subsection {* Security State Machine *}
locale SM =
  fixes s0 :: 's
  fixes is_execute :: "'e \<Rightarrow> bool"
  fixes is_grant :: "'e \<Rightarrow> bool"
  fixes step :: "'s \<Rightarrow> 'e \<Rightarrow> 's"
  fixes domain :: "'s \<Rightarrow> 'e \<Rightarrow> ('d option)"
  fixes grant_dest :: "'s \<Rightarrow> 'e \<Rightarrow> ('d option)"
  fixes vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sim> _ \<sim> _)")
  fixes interferes :: "'d \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> bool" ("(_ @ _ \<leadsto>_)")
  (*fixes dom_eq :: "'s \<Rightarrow> 's \<Rightarrow> 'e \<Rightarrow> bool" *)
  assumes 
    vpeq_transitive_lemma : "\<forall> s t r d. (s \<sim> d \<sim> t) \<and> (t \<sim> d \<sim> r) \<longrightarrow> (s \<sim> d \<sim> r)" and
    vpeq_symmetric_lemma : "\<forall> s t d. (s \<sim> d \<sim> t) \<longrightarrow> (t \<sim> d \<sim> s)" and
    vpeq_reflexive_lemma : "\<forall> s d. (s \<sim> d \<sim> s)" and
    (*domain_vpeq_lemma : "\<forall> s t a . (domain s a) = (domain t a)" and*)
    (*domain_vpeq_lemma : "\<forall> s t a . dom_eq s t a \<longrightarrow> (domain s a) = (domain t a)" and*)
    interf_reflexive: "\<forall>d s. (d @ s \<leadsto> d)" and
    execute_exclusive: "\<forall>a. is_execute a  \<longleftrightarrow> \<not>(is_grant a)" and
    grant_exclusive: "\<forall>a. is_grant a   \<longleftrightarrow> \<not>(is_execute a)"
begin
   
    definition non_interferes ::  "'d \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> bool" ("(_ @ _ \<setminus>\<leadsto> _)")
      where "(u @ s \<setminus>\<leadsto> v) \<equiv> \<not>(u @ s \<leadsto> v)"

    definition ivpeq :: "'s \<Rightarrow> 'd set \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<approx> _ \<approx> _)")
      where "ivpeq s D t \<equiv> \<forall> d \<in> D. (s \<sim> d \<sim> t)"

    primrec run :: "'s \<Rightarrow> 'e list \<Rightarrow> 's"
      where run_Nil: "run s [] = s" |
            run_Cons: "run s (a#as) = run (step s a) as "

    definition reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("(_ \<hookrightarrow> _)" [70,71] 60) where
      "reachable s1 s2 \<equiv>  (\<exists>as. run s1 as = s2 )"
    
    definition reachable0 :: "'s \<Rightarrow> bool"  where
      "reachable0 s \<equiv> reachable s0 s"
      
    declare non_interferes_def[cong] and ivpeq_def[cong] and reachable_def[cong]
            and reachable0_def[cong] and run.simps(1)[cong] and run.simps(2)[cong]

    lemma reachable_s0 : "reachable0 s0"
      by (metis SM.reachable_def SM_axioms reachable0_def run.simps(1)) 

    
    lemma reachable_self : "reachable s s"
      using reachable_def run.simps(1) by fastforce

    lemma reachable_step : "s' = step s a \<Longrightarrow> reachable s s'"
      proof-
        assume a0: "s' = step s a"
        then have "s' = run s [a]" by auto          
        then show ?thesis using reachable_def by blast 
      qed

    lemma run_trans : "\<forall>C T V as bs. T = run C as \<and> V = run T bs \<longrightarrow> V = run C (as@bs)"
     proof -
      {
        fix T V as bs
        have "\<forall>C. T = run C as \<and> V = run T bs \<longrightarrow> V = run C (as@bs)"
          proof(induct as)
            case Nil show ?case by simp
          next
            case (Cons c cs)
            assume a0: "\<forall>C. T = run C cs \<and> V = run T bs \<longrightarrow> V = run C (cs @ bs)"
            show ?case
              proof-
              {
                fix C
                have "T = run C (c # cs) \<and> V = run T bs \<longrightarrow> V = run C ((c # cs) @ bs) "
                  proof
                    assume b0: "T = run C (c # cs) \<and> V = run T bs"
                    from b0 obtain C' where b2: "C' = step C c \<and> T = run C' cs" by auto
                    with a0 b0 have "V = run C' (cs@bs)" by blast
                    with b2 show "V = run C ((c # cs) @ bs)"
                      using append_Cons run_Cons by auto 
                  qed
              }
              then show ?thesis by blast
              qed
          qed
      }
      then show ?thesis by auto
      qed

    lemma reachable_trans : "\<lbrakk>reachable C T; reachable T V\<rbrakk> \<Longrightarrow> reachable C V"
      proof-
        assume a0: "reachable C T"
        assume a1: "reachable T V"
        from a0 have "C = T \<or> (\<exists>as. T = run C as)" by auto
        then show ?thesis
          proof
            assume b0: "C = T"
            show ?thesis 
              proof -
                from a1 have "T = V \<or> (\<exists>as. V = run T as)" by auto
                then show ?thesis
                  proof
                    assume c0: "T=V"
                    with a0 show ?thesis by auto
                  next
                    assume c0: "(\<exists>as. V = run T as)"
                    then show ?thesis using a1 b0 by auto 
                  qed
              qed
          next
            assume b0: "\<exists>as. T = run C as"
            show ?thesis
              proof -
                from a1 have "T = V \<or> (\<exists>as. V = run T as)" by auto
                then show ?thesis
                  proof
                    assume c0: "T=V"
                    then show ?thesis using a0 by auto 
                  next
                    assume c0: "(\<exists>as. V = run T as)"
                    from b0 obtain as where d0: "T = run C as" by auto
                    from c0 obtain bs where d1: "V = run T bs" by auto
                    then show ?thesis using d0  run_trans by fastforce
                  qed
              qed
          qed
      qed

    lemma reachableStep : "\<lbrakk>reachable0 C; C' = step C a\<rbrakk> \<Longrightarrow> reachable0 C'"
      apply (simp add: reachable0_def)
      using reachable_step reachable_trans by blast
    
    lemma reachable0_reach : "\<lbrakk>reachable0 C; reachable C C'\<rbrakk> \<Longrightarrow> reachable0 C'"
      using  reachable_trans by fastforce

    declare reachable_def[cong del] and reachable0_def[cong del]
end

subsection{* Information flow security properties *}

locale SM_enabled = SM s0 is_execute is_grant step domain grant_dest vpeq interferes
  for s0 :: 's and
       is_execute :: "'e \<Rightarrow> bool" and
       is_grant :: "'e \<Rightarrow> bool" and
       step :: "'s \<Rightarrow> 'e \<Rightarrow> 's" and
       domain :: "'s \<Rightarrow> 'e \<Rightarrow> ('d option)" and
       grant_dest :: "'s \<Rightarrow> 'e \<Rightarrow> ('d option)" and
       vpeq :: "'s \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> bool"  ("(_ \<sim> _ \<sim> _)") and
       interferes :: "'d \<Rightarrow> 's \<Rightarrow> 'd \<Rightarrow> bool" ("(_ @ _ \<leadsto>_)")
  +
  assumes enabled0: "\<forall>s a. reachable0 s \<longrightarrow> (\<exists> s'. s' = step s a)"
begin

    lemma enabled : "reachable0 s \<Longrightarrow> (\<exists> s'. s' = step s a)"
        using enabled0 by simp

    primrec sources :: "'e list \<Rightarrow> 'd \<Rightarrow> 's \<Rightarrow> 'd set" where
      sources_Nil:"sources [] d s = {d}" |
      sources_Cons:"sources (a # as) d s = (\<Union>{sources as d (step s a)}) \<union> 
                              {w . w = the (domain s a) \<and> is_execute a \<and> (\<exists>v . interferes w s v \<and> v\<in>sources as d (step s a))}"
    declare sources_Nil [simp del]
    declare sources_Cons [simp del]

    
    
    primrec ipurge :: "'e list \<Rightarrow> 'd \<Rightarrow> 's  \<Rightarrow> 'e list" where
      ipurge_Nil:   "ipurge [] u s = []" |
      ipurge_Cons:  "ipurge (a#as) u s = (if (is_execute a \<and> the (domain s a) \<in> (sources (a#as) u s))  \<or>
                                                    (is_grant a \<and> the (grant_dest s a) \<in> (sources (a#as) u s) ) then
                                              a # ipurge as u (step s a)
                                           else
                                              ipurge as u (step s a)
                                          )"

     definition observ_equivalence :: "'s \<Rightarrow> 'e list \<Rightarrow> 's \<Rightarrow> 
          'e list \<Rightarrow> 'd \<Rightarrow> bool" ("(_ \<lhd> _ \<cong> _ \<lhd> _ @ _)")
      where "observ_equivalence s as t bs d \<equiv> 
               ((run s as) \<sim> d \<sim> (run t bs))"
     declare observ_equivalence_def[cong]

     lemma observ_equiv_sym:
       "(s \<lhd> as \<cong> t \<lhd> bs @ d) \<Longrightarrow> (t \<lhd> bs \<cong> s \<lhd> as @ d)"
       using observ_equivalence_def vpeq_symmetric_lemma by blast

     lemma observ_equiv_trans:
      "\<lbrakk>reachable0 t; (s \<lhd> as \<cong> t \<lhd> bs @ d); (t \<lhd> bs \<cong> x \<lhd> cs @ d)\<rbrakk> \<Longrightarrow> (s \<lhd> as \<cong> x \<lhd> cs @ d)"
        using observ_equivalence_def vpeq_transitive_lemma by blast

     definition noninfluence::"bool" 
       where "noninfluence \<equiv> \<forall> d as s t. reachable0 s \<and> reachable0 t
                                \<and> (s \<approx> (sources as d s) \<approx> t)
                                \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> (ipurge as d t) @ d)"

     definition noninterference :: "bool"
      where "noninterference \<equiv> \<forall>d as. (s0 \<lhd> as \<cong> s0 \<lhd> (ipurge as d s0) @ d)"

     definition noninterference_r :: "bool"
      where "noninterference_r \<equiv> \<forall>d as s. reachable0 s \<longrightarrow> (s \<lhd> as \<cong> s \<lhd> (ipurge as d s) @ d)"

     definition nonleakage :: "bool" 
      where "nonleakage \<equiv> \<forall>d as s t. reachable0 s \<and> reachable0 t
                                      \<and> (s \<approx> (sources as d s) \<approx> t) \<longrightarrow> (s \<lhd> as \<cong> t \<lhd> as @ d)"

subsection{* Unwinding conditions*}

     definition weakly_step_consistent :: "bool" where 
        "weakly_step_consistent \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and>
                              (s \<sim> (the (domain s a)) \<sim> t) \<longrightarrow> ((step s a) \<sim> d \<sim> (step t a))"

     definition dynamic_local_respect :: "bool" where
        "dynamic_local_respect \<equiv> \<forall>a d s. reachable0 s \<and> \<not>((the (domain s a)) @ s \<leadsto> d) \<longrightarrow> (s \<sim> d \<sim> (step s a)) "

     definition policy_respect :: "bool" where
        "policy_respect \<equiv> \<forall>a u s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> u \<sim> t) \<longrightarrow> (interferes (the (domain s a)) s u = interferes (the (domain t a)) t u)"
                                                  
     definition weakly_grant_step_consistent :: "bool" where
        "weakly_grant_step_consistent \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> is_grant a \<and> (s \<sim> d \<sim> t) \<and>
                              (s \<sim> (the (grant_dest s a)) \<sim> t) \<longrightarrow> ((step s a) \<sim> d \<sim> (step t a))"

     definition grant_local_respect :: "bool" where
        "grant_local_respect \<equiv>  \<forall>s v a. reachable0 s \<and> \<not>(v = the (grant_dest s a)) \<and> is_grant a \<longrightarrow> 
                                (s \<sim> v \<sim> (step s a))"

     definition domain_equal :: "bool" where
        "domain_equal \<equiv>  \<forall>s t a. reachable0 s \<and> reachable0 t \<and>  (s \<sim> (the (domain s a)) \<sim> t)  \<longrightarrow> 
                                (domain s a) = (domain t a)"
     
     definition grant_dest_equal :: "bool" where
        "grant_dest_equal \<equiv>  \<forall>s t a. reachable0 s \<and> reachable0 t \<and>  (s \<sim> (the (grant_dest s a)) \<sim> t)  \<longrightarrow> 
                                (grant_dest s a) = (grant_dest t a)"

     declare weakly_step_consistent_def [cong] and dynamic_local_respect_def [cong] and policy_respect_def [cong]
              and weakly_grant_step_consistent_def [cong] and grant_local_respect_def and domain_equal_def

     definition lemma_local :: "bool" where
        "lemma_local \<equiv> \<forall>s a as u. the (domain s a) \<notin> sources (a # as) u s \<longrightarrow> (s \<approx> (sources (a # as) u s)  \<approx> (step s a))"                                     
     
     
     lemma sources_refl:"reachable0 s \<Longrightarrow> u \<in> sources as u s"
      apply(induct as arbitrary: s)
       apply(simp add: sources_Nil)
      apply(simp add: sources_Cons) 
      using enabled reachableStep  
        by metis

     lemma sources_eq2: "(s \<sim> u \<sim> t) \<longrightarrow> ((sources as u s) = (sources as u t))"
       apply (induct as)
       apply (simp add: sources_Nil)
       apply (simp add: sources_Cons)

       oops
     
subsection{* Inference framework of information flow security properties *}

    lemma noninf_impl_nonintf_r: "noninfluence \<Longrightarrow> noninterference_r"
      using ivpeq_def noninfluence_def noninterference_r_def vpeq_reflexive_lemma by blast    

    lemma noninf_impl_nonlk: "noninfluence \<Longrightarrow> nonleakage"
      using noninterference_r_def nonleakage_def observ_equiv_sym 
        observ_equiv_trans noninfluence_def noninf_impl_nonintf_r by blast   

    theorem nonintf_r_impl_noninterf: "noninterference_r \<Longrightarrow> noninterference"
      using noninterference_def noninterference_r_def reachable_s0 by auto 

     lemma lemma_1_sub_1 : "\<lbrakk>reachable0 s ;
                       dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       the (domain s a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> (step s a))"
        apply (simp add:dynamic_local_respect_def sources_Cons)
        by blast

     lemma lemma_1_sub_2 : "\<lbrakk>reachable0 s ;
                       reachable0 t ;
                       dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       the (domain s a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>       
                      \<Longrightarrow> (t \<approx> (sources as u (step s a)) \<approx> (step t a))"
        apply (simp)
        apply (erule allE)                 
        apply (simp add:sources_Cons)      
        by blast

     lemma lemma_1_sub_2_1 : "\<lbrakk>reachable0 s ;
                       reachable0 t ;
                       dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       \<forall>v.\<not>interferes (the (domain s a)) s v \<and> v\<in>sources as u (step s a);
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>       
                      \<Longrightarrow> (t \<approx> (sources as u (step s a)) \<approx> (step t a))"
        apply (simp)
        apply (erule allE)
        apply (simp add:sources_Cons)
        by blast
     
     lemma lemma_1_sub_3 : "\<lbrakk>is_execute a;
                       the (domain s a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>     
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> t)"
         apply (simp add:sources_Cons)
         apply (simp add:sources_Cons)
         done

     lemma lemma_1_sub_4 : "\<lbrakk>(s \<approx> (sources as u (step s a)) \<approx> t);
                             (s \<approx> (sources as u (step s a)) \<approx> (step s a));
                             (t \<approx> (sources as u (step s a)) \<approx> (step t a)) \<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx>(sources as u (step s a)) \<approx> (step t a))"
       by (meson ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
           

     lemma lemma_1 : "\<lbrakk>reachable0 s;
                      reachable0 t;
                      weakly_step_consistent;
                      dynamic_local_respect;
                      policy_respect;
                      (s \<approx> (sources (a # as) u s) \<approx> t);
                      is_execute a\<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
       apply (case_tac "the (domain s a)\<in>sources (a # as) u s")
       apply (simp add:weakly_step_consistent_def)
       apply (simp add:sources_Cons)                                                        
         proof -
           assume a1: dynamic_local_respect
           assume a2: policy_respect
           assume a3: "is_execute a"
           assume a4: "the (domain s a) \<notin> sources (a # as) u s"
           assume a5: "(s \<approx> (sources (a # as) u s) \<approx> t)"
           assume b0: "reachable0 s"
           assume b1: "reachable0 t"

           have a6:"(s \<approx> (sources as u (step s a)) \<approx> t)"
            using a1 a2 a3 a4 a5 lemma_1_sub_3 by auto
           then have a7: "(s \<approx> (sources as u (step s a)) \<approx> (step s a))"
            using b0 a1 a2 a3 a4 a5 lemma_1_sub_1 by auto
           then have a8: "(t \<approx> (sources as u (step s a)) \<approx> (step t a))"
            using b1 b0 a1 a2 a3 a4 a5 lemma_1_sub_2 by auto
           then show " ((step s a) \<approx>(sources as u (step s a)) \<approx> (step t a))"
            using a6 a7 lemma_1_sub_4 by blast
         qed

     lemma lemma_2 : "\<lbrakk>reachable0 s;
                      dynamic_local_respect;
                      the (domain s a) \<notin> sources (a # as) u s;
                      is_execute a\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> (step s a))"
       apply (simp add:dynamic_local_respect_def)
       apply (simp add:sources_Cons)
       by blast

     lemma lemma_3_sub_1: "is_grant a \<Longrightarrow> (sources (a # as) u s) =  (sources as u (step s a))"
        apply (simp add:sources_Cons)
        using grant_exclusive
        by blast

     lemma lemma_3_sub_2: "\<lbrakk>reachable0 s;
                      reachable0 t;
                      weakly_grant_step_consistent;    
                      (s \<approx> D \<approx> t);
                     the (grant_dest s a) \<in> D;
                      is_grant a\<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx> D \<approx> (step t a))"
        apply (simp add:weakly_grant_step_consistent_def)
        by auto

     lemma lemma_3: "\<lbrakk>\<forall>a s t u as. reachable0 s;
                      reachable0 t;
                      weakly_grant_step_consistent;    
                      (s \<approx> (sources (a # as) u s) \<approx> t);
                      the (grant_dest s a) \<in> (sources (a # as) u s);
                      is_grant a\<rbrakk>
                      \<Longrightarrow> ((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
       apply (simp add: weakly_grant_step_consistent_def)
       apply (simp add: sources_Cons)
       done
     
     lemma lemma_4_sub_2 : "\<forall>a v A. a \<notin> A \<Longrightarrow> v \<in> A \<longrightarrow> a \<noteq> v  "
        by blast

     lemma lemma_4_sub3 : "the (grant_dest s a) \<notin> (sources (a # as) u s) \<Longrightarrow>  v \<in> (sources (a # as) u s) \<longrightarrow> the (grant_dest s a) \<noteq> v  "
        by blast

     lemma lemma_4_sub_1: "\<lbrakk>\<forall>a s D. is_grant a;
                      reachable0 s;
                      grant_local_respect;
                      the (grant_dest s a) \<notin> D\<rbrakk>
                      \<Longrightarrow> (s \<approx> D \<approx> (step s a))"
       using grant_local_respect_def by force

     lemma lemma_4: "\<lbrakk>\<forall>a s u as. is_grant a;
                      reachable0 s; 
                      grant_local_respect;
                      the (grant_dest s a) \<notin> (sources (a # as) u s)\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources (a # as) u s) \<approx> (step s a))"
       using grant_local_respect_def by force

     lemma sources_eq1: "\<forall>s t as u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    policy_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    domain_equal \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (sources as u s) = (sources as u t)"
       proof -
       {
        fix as
        have "\<forall>s t u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    policy_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    domain_equal \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (sources as u s) = (sources as u t)"
          proof(induct as)
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) 
                                \<and> (reachable0 t) 
                                \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect 
                                \<and> policy_respect 
                                \<and> weakly_grant_step_consistent 
                                \<and> grant_local_respect 
                                \<and> domain_equal 
                                \<and> (s \<approx> (sources bs u s) \<approx> t)) \<longrightarrow>
                                  (sources bs u s) = (sources bs u t)"
            then show ?case
              proof -
              {
                 fix s t u
                 assume p1: "reachable0 s"
                 assume p2: "reachable0 t"
                 assume p3: weakly_step_consistent
                 assume p4: policy_respect
                 assume p5: "dynamic_local_respect"
                 assume p6: "weakly_grant_step_consistent"
                 assume p7: "grant_local_respect"
                 assume p8: "domain_equal"
                 assume p9: "(s \<approx> (sources (b # bs) u s) \<approx> t)" 
                 have "sources (b # bs) u s = sources (b # bs) u t "
                   proof (cases "is_execute b")
                     assume a0: "is_execute b "
                     have a2: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                       using a0 lemma_1 p1 p2 p3 p4 p5 p9 by blast
                     show "sources (b # bs) u s = sources (b # bs) u t"
                       proof (cases "the (domain s b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (domain s b) \<in> (sources (b # bs) u s)"
                         have b1: "s \<sim> (the(domain s b)) \<sim> t"
                           using b0 p9 by auto
                         have b2: "(domain s b) = (domain t b)"
                           using b1 domain_equal_def p1 p2 p8 by blast
                         have b3: "interferes (the (domain s b)) s u = interferes (the (domain t b)) t u "
                           using p1 p2 p4 p9 sources_refl by fastforce
                         have b4: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           using a2 p0 p1 p2 p3 p4 p5 p6 p7 p8 reachableStep by blast
                         have b5: "\<forall>v. v\<in>sources bs u (step s b) 
                              \<longrightarrow> interferes (the (domain s b)) s v = interferes (the (domain t b)) t v "
                           using p1 p2 ivpeq_def p4 p9 sources_Cons by fastforce
                         then show "sources (b # bs) u s = sources (b # bs) u t"
                           using b4 b2 b5 sources_Cons by auto
                       next
                         assume b0: "the (domain s b) \<notin> (sources (b # bs) u s)"
                         have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           using b0 sources_Cons by auto
                         have b2: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           using a2 p0 p1 p2 p3 p4 p5 p6 p7 p8 reachableStep by blast
                         have b3: "\<forall>v. v\<in>sources bs u (step s b)\<longrightarrow>\<not> interferes (the (domain s b)) s v "
                           using a0 b0 sources_Cons by auto
                         have b4: "\<forall>v. v\<in>sources bs u (step s b)\<longrightarrow>\<not> interferes (the (domain t b)) t v "
                           using p1 p2 b1 b3 ivpeq_def p4 p9 policy_respect_def by blast
                         have b5: "\<forall>v. v\<in>sources bs u (step t b)\<longrightarrow>\<not> interferes (the (domain t b)) t v "
                           by (simp add: b2 b4)
                         have b7: "sources (b # bs) u t = sources bs u (step t b)"
                           proof -
                             have "\<forall>s p pa f pb pc fa e es d sa. \<not> SM_enabled (s::'s) p pa f pb pc \<or> SM_enabled.sources p f fa pc ((e::'e) # es) (d::'d) sa = \<Union>{SM_enabled.sources p f fa pc es d (f sa e)} \<union> {da. da = the (fa sa e) \<and> p e \<and> (\<exists>db. pc da sa db \<and> db \<in> SM_enabled.sources p f fa pc es d (f sa e))}"
                               by (simp add: SM_enabled.sources.simps(2))
                             then show ?thesis
                               using SM_enabled_axioms b2 b4 interf_reflexive by auto
                           qed
                         then show ?thesis
                           by (simp add: b1 b2)
                         qed
                     next
                       assume a0: "\<not> is_execute b "
                       have a1: "sources (b # bs) u s = sources bs u (step s b)"
                         by (simp add: a0 sources_Cons)
                       have a2: "sources (b # bs) u t = sources bs u (step t b)"
                         by (simp add: a0 sources_Cons)
                       have a3: "is_grant b"
                         using a0 execute_exclusive by auto
                       have a4: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                         proof (cases "the (grant_dest s b) \<in> (sources (b # bs) u s)")
                           assume b0: "the (grant_dest s b) \<in> (sources (b # bs) u s)"
                           show "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                             using a1 a3 b0 p1 p2 p6 p9 by auto
                         next
                           assume b1: "the (grant_dest s b) \<notin> sources (b # bs) u s"
                           have "(s \<approx> (sources (b # bs) u s) \<approx> (step s b))"
                             using a3 b1 grant_local_respect_def p1 p7 by force
                           show ?thesis
                             by (smt a1 a3 grant_local_respect_def ivpeq_def lemma_1_sub_4
                               p1 p2 p6 p7 p9 vpeq_symmetric_lemma weakly_grant_step_consistent_def)
                         qed
                       show ?thesis
                         using a1 a2 a4 p0 p1 p2 p3 p4 p5 p6 p7 p8 reachableStep by blast
                   qed
              }
              then show ?thesis by blast
              qed
          qed

       }
       then show ?thesis by blast
       qed

    lemma ipurge_eq: "\<forall>s t as u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    policy_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    domain_equal \<and>
                    grant_dest_equal \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (ipurge as u s) = (ipurge as u t)"
       proof -
       {
        fix as
        have "\<forall>s t u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    policy_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    domain_equal \<and>
                    grant_dest_equal \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (ipurge as u s) = (ipurge as u t)"
          proof(induct as)
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) 
                                \<and> (reachable0 t) 
                                \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect 
                                \<and> policy_respect 
                                \<and> weakly_grant_step_consistent 
                                \<and> grant_local_respect
                                \<and> domain_equal 
                                \<and> grant_dest_equal 
                                \<and> (s \<approx> (sources bs u s) \<approx> t))
                                \<longrightarrow> (ipurge bs u s) = (ipurge bs u t)"
            then show ?case
              proof -
              {
                 fix s t u
                 assume p1: "reachable0 s"
                 assume p2: "reachable0 t"
                 assume p3: weakly_step_consistent
                 assume p4: policy_respect
                 assume p5: "dynamic_local_respect"
                 assume p6: "weakly_grant_step_consistent"
                 assume p7: "grant_local_respect"
                 assume p8: "domain_equal"
                 assume p9: "(s \<approx> (sources (b # bs) u s) \<approx> t)"
                 assume p10: "grant_dest_equal"
                 have "ipurge (b # bs) u s = ipurge (b # bs) u t "
                   proof (cases "is_execute b")
                     assume a0: "is_execute b"
                     have a1: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                       using a0 lemma_1 p1 p2 p3 p4 p5 p9 by blast
                     have a2: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                       using a1 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 reachableStep by blast
                     have a3: "sources (b # bs) u s = sources (b # bs) u t"
                       using p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1 by blast
                     then show ?thesis
                       proof (cases "the (domain s b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (domain s b) \<in> (sources (b # bs) u s)"
                         have b1: "s \<sim> (the(domain s b)) \<sim> t"
                           using b0 p9 by auto
                         have b2: "(domain s b) = (domain t b)"
                           using b1 domain_equal_def p1 p2 p8 by blast
                         have b3: "the (domain t b) \<in> (sources (b # bs) u t)"
                           using a3 b0 b2 by auto
                         then show ?thesis
                           using a0 a2 b0 ipurge_Cons by auto
                       next
                         assume b0: "the (domain s b) \<notin> (sources (b # bs) u s)"
                         have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           using b0 sources_Cons by auto
                         have b3: "\<forall>v. v\<in>sources bs u (step s b)\<longrightarrow>\<not> interferes (the (domain s b)) s v "
                           using a0 b0 sources_Cons by auto
                         have b4: "\<forall>v. v\<in>sources bs u (step s b)\<longrightarrow>\<not> interferes (the (domain t b)) t v "
                           using p1 p2 b1 b3 ivpeq_def p4 p9 policy_respect_def by blast
                         have b5: "the (domain t b) \<notin> (sources (b # bs) u t)"
                           using a3 b1 b4 interf_reflexive by auto
                         have b6: "ipurge (b # bs) u s = ipurge bs u (step s b)"
                           using a0 b0 execute_exclusive by auto
                         have b7: "ipurge (b # bs) u t = ipurge bs u (step t b)"
                           using a0 b5 execute_exclusive by auto
                         then show ?thesis
                           using b6 b7 a2 by auto 
                       qed
                   next
                     assume a0: "\<not> is_execute b "
                     have a1: "is_grant b"
                       using a0 execute_exclusive by auto
                     then show ?thesis
                       proof (cases "the (grant_dest s b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (grant_dest s b) \<in> (sources (b # bs) u s)"
                         have b1: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a1 b0 lemma_3_sub_1 p1 p2 p6 p9 by auto
                         have b2: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b1 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 reachableStep by blast
                         have b3: "(grant_dest s b) = (grant_dest t b)"
                           using b0 grant_dest_equal_def ivpeq_def p1 p10 p2 p9 by blast
                         then show ?thesis
                           by (metis a1 b0 b2 ipurge_Cons p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1)
                       next
                         assume b0: "the (grant_dest s b) \<notin> (sources (b # bs) u s)"
                         have b1: "sources (b # bs) u s = sources bs u (step s b)"
                           by (simp add: a0 sources_Cons)
                         have b2: "(s \<approx> (sources (b # bs) u s) \<approx> (step s b))"
                           using a1 b0 grant_local_respect_def p1 p7 by force
                         have b3: "ipurge (b # bs) u s = ipurge bs u (step s b)"
                           using a0 b0 by auto
                         have b4: "the (grant_dest t b) \<notin> (sources (b # bs) u t)"
                           by (metis b0 grant_dest_equal_def ivpeq_def p1 p10 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1 vpeq_symmetric_lemma)
                         have b5: "ipurge (b # bs) u t = ipurge bs u (step t b)"
                           using a0 b4 by auto
                         have b6: "(t \<approx> (sources (b # bs) u t) \<approx> (step t b))"
                           using a1 b4 grant_local_respect_def p2 p7 by force
                         have b7: "((step s b) \<approx> (sources (b # bs) u t) \<approx> (step t b))"
                           by (metis (full_types) b1 b2 b6 lemma_1_sub_4 p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1)
                         have b8: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           by (metis b1 b7 p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1)
                         have b9: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b8 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 reachableStep by blast
                         then show ?thesis
                           using b3 b5 b9 by auto
                         qed
                     qed
              }
              then show ?thesis by blast
              qed
          qed
       }
       then show ?thesis by blast
       qed

    lemma non_influgence_lemma: "\<forall>s t as u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    policy_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    domain_equal \<and>
                    grant_dest_equal \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
      proof -
      { 
        fix as
        have  "\<forall>s t u. reachable0 s \<and>
                    reachable0 t \<and>
                    weakly_step_consistent \<and>
                    dynamic_local_respect \<and>
                    policy_respect \<and>
                    weakly_grant_step_consistent \<and>
                    grant_local_respect \<and>
                    domain_equal \<and>
                    grant_dest_equal \<and>
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
          proof (induct as)
            case Nil show ?case using sources_Nil by auto
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) 
                                \<and> (reachable0 t) 
                                \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect 
                                \<and> policy_respect 
                                \<and> weakly_grant_step_consistent 
                                \<and> grant_local_respect
                                \<and> domain_equal
                                \<and> grant_dest_equal
                                \<and> (s \<approx> (sources bs u s) \<approx> t)) \<longrightarrow>
                                  ((s \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
            then show ?case
              proof -
              { 
                fix s t u
                assume p1: "reachable0 s"
                assume p2: "reachable0 t"
                assume p3: weakly_step_consistent
                assume p4: dynamic_local_respect
                assume p5: policy_respect
                assume p6: weakly_grant_step_consistent
                assume p7: grant_local_respect
                assume p8: "(s \<approx> (sources (b # bs) u s) \<approx> t)"
                assume p9: domain_equal
                assume p10: grant_dest_equal
                have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) u t @ u"
                  proof (cases "is_execute b")
                    assume a0: "is_execute b"
                    have a1: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                      using a0 lemma_1 p1 p2 p3 p4 p5 p8 by blast
                    then show ?thesis
                      proof (cases "the (domain s b) \<in> sources (b # bs) u s")
                        assume b0: "the (domain s b) \<in> sources (b # bs) u s"
                        have b1: "interferes (the (domain s b)) s u = interferes (the (domain t b)) t u "
                          using p1 p2 p5 p8 sources_refl by fastforce
                        have b2: "\<forall>v. v\<in>sources bs u (step s b) 
                              \<longrightarrow> interferes (the (domain s b)) s v = interferes (the (domain t b)) t v "
                          using p1 p2 ivpeq_def p5 p8 sources_Cons by fastforce
                        have b3: "ipurge (b # bs) u t = b # (ipurge bs u (step t b))"
                          by (metis a0 b0 domain_equal_def ipurge_Cons ivpeq_def p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1)
                        have b4: "(((step s b) \<lhd> bs \<cong> (step t b) \<lhd> (ipurge bs u (step t b)) @ u))"
                          using a1 p0 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                        then show ?thesis
                          using b3 b4 by auto
                      next
                        assume b0: "the (domain s b) \<notin> sources (b # bs) u s"
                        have b1: "ipurge (b # bs) u t = (ipurge bs u (step t b))"
                          by (metis a0 a1 b0 execute_exclusive ipurge_Cons ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p8 p9 reachableStep)
                        have b2: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                          using a0 b0 lemma_2 p1 p4 by blast
                        have b3:"(s \<approx> (sources bs u (step s b)) \<approx> t)"
                          using a0 b0 lemma_1_sub_3 p8 by blast
                        have b4: "((step s b) \<approx> (sources bs u (step s b)) \<approx> t)"
                          by (meson b3 b2 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                        have b5: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
                          using b4 p0 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                        have b6: "(t \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                          using p1 p2 a0 b0 lemma_1_sub_2 p4 p5 p8 by blast
                        have b7: "ipurge bs u t = ipurge bs u (step t b)"
                          by (metis a1 b4 ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep)
                        have b8: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u (step t b)) @ u))"
                          using b5 b7 by auto
                        then show ?thesis
                          using b1 observ_equivalence_def run_Cons by auto
                      qed
                   next
                     assume a0: "\<not> is_execute b "
                     have a1: "is_grant b"
                       using a0 execute_exclusive by auto
                     then show ?thesis
                       proof (cases "the (grant_dest s b) \<in> (sources (b # bs) u s)")
                         assume b0: "the (grant_dest s b) \<in> (sources (b # bs) u s)"
                         have b1: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           using a1 b0 lemma_3_sub_1 p1 p2 p6 p8 by auto
                         have b2: "(ipurge bs u (step s b)) = (ipurge bs u (step t b))"
                           using b1 ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         have b3: "ipurge (b # bs) u t = b # (ipurge bs u (step t b))"
                           by (metis a1 b0 b2 ipurge_Cons ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p8 p9)
                         have b4: "(step s b) \<lhd> bs \<cong> (step t b) \<lhd> ipurge bs u (step t b) @ u "
                           using p0 b1 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         then show ?thesis
                           using b3 observ_equivalence_def run_Cons by auto
                       next
                         assume b0: "the (grant_dest s b) \<notin> (sources (b # bs) u s)"
                         have b1: "the (grant_dest t b) \<notin> (sources (b # bs) u t)"
                           by (metis b0 grant_dest_equal_def ivpeq_def p1 p10 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1 vpeq_symmetric_lemma)
                         have b2: "ipurge (b # bs) u t = (ipurge bs u (step t b))"
                           by (simp add: a0 b1)
                         have b3: "(s \<approx> (sources bs u (step s b)) \<approx> (step s b))"
                           by (metis a1 b0 grant_local_respect_def ivpeq_def lemma_3_sub_1 p1 p7)
                         have b4: "(t \<approx> (sources bs u (step t b)) \<approx> (step t b))"
                           by (metis a1 b1 grant_local_respect_def ivpeq_def lemma_3_sub_1 p2 p7)
                         have b5: "(sources bs u (step s b)) = (sources bs u (step t b))"
                           using a1 lemma_3_sub_1 p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1 by blast
                         have b6: "(s \<approx> (sources bs u (step s b)) \<approx> t)"
                           using a1 lemma_3_sub_1 p8 by auto
                         have b7: "((step s b) \<approx> (sources bs u (step s b)) \<approx> t)"
                           by (meson b3 b6 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                         have b8: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
                           using b7 p0 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         have b9: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                           by (metis b3 b4 b5 b6 lemma_1_sub_4)
                         have b10: "ipurge bs u t = ipurge bs u (step t b)"
                           by (metis b9 b7 ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep)
                         have b11: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs u (step t b)) @ u))"
                           using b8 b10 by auto
                         then show ?thesis
                           using b2 observ_equivalence_def run_Cons by auto
                       qed
                   qed
              }
              then show ?thesis by blast
              qed
          qed
       }
       then show ?thesis by blast
       qed


    theorem UnwindingTheorem : "\<lbrakk>weakly_step_consistent;
                            dynamic_local_respect;
                            policy_respect;
                            weakly_grant_step_consistent;
                            grant_local_respect;
                            domain_equal;
                            grant_dest_equal\<rbrakk> 
                            \<Longrightarrow> noninfluence"
      proof -
        assume p3: weakly_step_consistent
        assume p4: dynamic_local_respect
        assume p5: policy_respect
        assume p6: weakly_grant_step_consistent
        assume p7: grant_local_respect
        assume p9: domain_equal
        assume p10: grant_dest_equal
        {
        fix as d
        have "\<forall>s t. reachable0 s \<and>
                  reachable0 t \<and>
                  (s \<approx> (sources as d s) \<approx> t)
                  \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as d  t) @ d))"
          proof(induct as)
            case Nil show ?case using sources_Nil by auto
          next
            case (Cons b bs)
            assume p0: "\<forall>s t. reachable0 s \<and>
                  reachable0 t \<and>
                  (s \<approx> (sources bs d s) \<approx> t)
                  \<longrightarrow> ((s \<lhd> bs \<cong> t \<lhd> (ipurge bs d  t) @ d))"
            then show ?case
              proof -
              { 
                fix s t
                assume p1: "reachable0 s"
                assume p2: "reachable0 t"
                assume p8: "(s \<approx> (sources (b # bs) d s) \<approx> t)"
                have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) d t @ d"
                  proof (cases "is_execute b")
                    assume a0: "is_execute b"
                    have a1: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                      using a0 lemma_1 p1 p2 p3 p4 p5 p8 by blast
                    then show ?thesis
                      proof (cases "the (domain s b) \<in> sources (b # bs) d s")
                        assume b0: "the (domain s b) \<in> sources (b # bs) d s"
                        have b1: "interferes (the (domain s b)) s d = interferes (the (domain t b)) t d "
                          using p1 p2 p5 p8 sources_refl by fastforce
                        have b2: "\<forall>v. v\<in>sources bs d (step s b) 
                              \<longrightarrow> interferes (the (domain s b)) s v = interferes (the (domain t b)) t v "
                          using p1 p2 ivpeq_def p5 p8 sources_Cons by fastforce
                        have b3: "ipurge (b # bs) d t = b # (ipurge bs d (step t b))"
                          by (metis a0 b0 domain_equal_def ipurge_Cons ivpeq_def p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1)
                        have b4: "(((step s b) \<lhd> bs \<cong> (step t b) \<lhd> (ipurge bs d (step t b)) @ d))"
                          using a1 p0 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                        then show ?thesis
                          using b3 b4 by auto
                      next
                        assume b0: "the (domain s b) \<notin> sources (b # bs) d s"
                        have b1: "ipurge (b # bs) d t = (ipurge bs d (step t b))"
                          by (metis a0 a1 b0 execute_exclusive ipurge_Cons ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p8 p9 reachableStep)
                        have b2: "(s \<approx> (sources bs d (step s b)) \<approx> (step s b))"
                          using a0 b0 lemma_2 p1 p4 by blast
                        have b3:"(s \<approx> (sources bs d (step s b)) \<approx> t)"
                          using a0 b0 lemma_1_sub_3 p8 by blast
                        have b4: "((step s b) \<approx> (sources bs d (step s b)) \<approx> t)"
                          by (meson b3 b2 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                        have b5: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d t) @ d))"
                          using b4 p0 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                        have b6: "(t \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                          using p1 p2 a0 b0 lemma_1_sub_2 p4 p5 p8 by blast
                        have b7: "ipurge bs d t = ipurge bs d (step t b)"
                          by (metis a1 b4 ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep)
                        have b8: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d (step t b)) @ d))"
                          using b5 b7 by auto
                        then show ?thesis
                          using b1 observ_equivalence_def run_Cons by auto
                      qed
                   next
                     assume a0: "\<not> is_execute b "
                     have a1: "is_grant b"
                       using a0 execute_exclusive by auto
                     then show ?thesis
                       proof (cases "the (grant_dest s b) \<in> (sources (b # bs) d s)")
                         assume b0: "the (grant_dest s b) \<in> (sources (b # bs) d s)"
                         have b1: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                           using a1 b0 lemma_3_sub_1 p1 p2 p6 p8 by auto
                         have b2: "(ipurge bs d (step s b)) = (ipurge bs d (step t b))"
                           using b1 ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         have b3: "ipurge (b # bs) d t = b # (ipurge bs d (step t b))"
                           by (metis a1 b0 b2 ipurge_Cons ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p8 p9)
                         have b4: "(step s b) \<lhd> bs \<cong> (step t b) \<lhd> ipurge bs d (step t b) @ d "
                           using p0 b1 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         then show ?thesis
                           using b3 observ_equivalence_def run_Cons by auto
                       next
                         assume b0: "the (grant_dest s b) \<notin> (sources (b # bs) d s)"
                         have b1: "the (grant_dest t b) \<notin> (sources (b # bs) d t)"
                           by (metis b0 grant_dest_equal_def ivpeq_def p1 p10 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1 vpeq_symmetric_lemma)
                         have b2: "ipurge (b # bs) d t = (ipurge bs d (step t b))"
                           by (simp add: a0 b1)
                         have b3: "(s \<approx> (sources bs d (step s b)) \<approx> (step s b))"
                           by (metis a1 b0 grant_local_respect_def ivpeq_def lemma_3_sub_1 p1 p7)
                         have b4: "(t \<approx> (sources bs d (step t b)) \<approx> (step t b))"
                           by (metis a1 b1 grant_local_respect_def ivpeq_def lemma_3_sub_1 p2 p7)
                         have b5: "(sources bs d (step s b)) = (sources bs d (step t b))"
                           using a1 lemma_3_sub_1 p1 p2 p3 p4 p5 p6 p7 p8 p9 sources_eq1 by blast
                         have b6: "(s \<approx> (sources bs d (step s b)) \<approx> t)"
                           using a1 lemma_3_sub_1 p8 by auto
                         have b7: "((step s b) \<approx> (sources bs d (step s b)) \<approx> t)"
                           by (meson b3 b6 ivpeq_def vpeq_symmetric_lemma vpeq_transitive_lemma)
                         have b8: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d t) @ d))"
                           using b7 p0 p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep by blast
                         have b9: "((step s b) \<approx> (sources bs d (step s b)) \<approx> (step t b))"
                           by (metis b3 b4 b5 b6 lemma_1_sub_4)
                         have b10: "ipurge bs d t = ipurge bs d (step t b)"
                           by (metis b9 b7 ipurge_eq p1 p10 p2 p3 p4 p5 p6 p7 p9 reachableStep)
                         have b11: "(((step s b) \<lhd> bs \<cong> t \<lhd> (ipurge bs d (step t b)) @ d))"
                           using b8 b10 by auto
                         then show ?thesis
                           using b2 observ_equivalence_def run_Cons by auto
                       qed
                   qed
              }
              then show ?thesis by blast
              qed
          qed
          }
      then show ?thesis using noninfluence_def by blast
    qed

end
