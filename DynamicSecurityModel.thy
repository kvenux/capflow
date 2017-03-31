theory DynamicSecurityModel
imports Main
begin

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
    domain_vpeq_lemma : "\<forall> s t a . (domain s a) = (domain t a)" and
    (*domain_vpeq_lemma : "\<forall> s t a . dom_eq s t a \<longrightarrow> (domain s a) = (domain t a)" and*)
    interf_reflexive: "\<forall>d s. (d @ s \<leadsto> d)" and
    execute_exclusive: "\<forall>a. is_execute a  \<longrightarrow> \<not>(is_grant a)" and
    grant_exclusive: "\<forall>a. is_grant a  \<longrightarrow> \<not>(is_execute a)"
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

     definition weakly_step_consistent :: "bool" where 
        "weakly_step_consistent \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> (s \<sim> d \<sim> t) \<and>
                              (s \<sim> (the (domain s a)) \<sim> t) \<longrightarrow> ((step s a) \<sim> d \<sim> (step t a))"

     definition dynamic_local_respect :: "bool" where
        "dynamic_local_respect \<equiv> \<forall>a d s. \<not>((the (domain s a)) @ s \<leadsto> d) \<longrightarrow> (s \<sim> d \<sim> (step s a)) "

     definition policy_respect :: "bool" where
        "policy_respect \<equiv> \<forall>a u s t. (s \<sim> u \<sim> t) \<longrightarrow> (interferes (the (domain s a)) s u = interferes (the (domain t a)) t u)"
                                                  
     definition weakly_grant_step_consistent :: "bool" where
        "weakly_grant_step_consistent \<equiv>  \<forall>a d s t. reachable0 s \<and> reachable0 t \<and> is_grant a \<and> (s \<sim> d \<sim> t) \<and>
                              (s \<sim> (the (grant_dest s a)) \<sim> t) \<longrightarrow> ((step s a) \<sim> d \<sim> (step t a))"

     definition grant_local_respect :: "bool" where
        "grant_local_respect \<equiv>  \<forall>s v a. reachable0 s \<and> \<not>(v = the (grant_dest s a)) \<and> is_grant a \<longrightarrow> 
                                (s \<sim> v \<sim> (step s a))"
     

     declare weakly_step_consistent_def [cong] and dynamic_local_respect_def [cong] and policy_respect_def [cong]
              and weakly_grant_step_consistent_def [cong] and grant_local_respect_def

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
     


     lemma lemma_1_sub_1 : "\<lbrakk>dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       the (domain s a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>
                      \<Longrightarrow> (s \<approx> (sources as u (step s a)) \<approx> (step s a))"
        apply (simp add:dynamic_local_respect_def sources_Cons)
        by blast

     lemma lemma_1_sub_2 : "\<lbrakk>dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       the (domain s a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>       
                      \<Longrightarrow> (t \<approx> (sources as u (step s a)) \<approx> (step t a))"
        apply (simp)
        apply (erule allE)                 
        apply (simp add:sources_Cons)      
        by blast

     lemma lemma_1_sub_2_1 : "\<lbrakk>dynamic_local_respect;
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
           

     lemma lemma_1_new_6 : "\<lbrakk>dynamic_local_respect;
                       policy_respect;
                       is_execute a;
                       the (domain s a) \<notin> sources (a # as) u s;
                       (s \<approx> (sources (a # as) u s) \<approx> t)\<rbrakk>       
                      \<Longrightarrow> ((step s a) \<approx>(sources as u (step s a)) \<approx> (step t a))"
         proof -
           assume a1: dynamic_local_respect
           assume a2: policy_respect
           assume a3: "is_execute a"
           assume a4: "the (domain s a) \<notin> sources (a # as) u s"
           assume a5: "(s \<approx> (sources (a # as) u s) \<approx> t)"

           have a6:"(s \<approx> (sources as u (step s a)) \<approx> t)"
            using a1 a2 a3 a4 a5 lemma_1_sub_3 by auto
           then have a7: "(s \<approx> (sources as u (step s a)) \<approx> (step s a))"
            using a1 a2 a3 a4 a5 lemma_1_sub_1 by auto
           then have a8: "(t \<approx> (sources as u (step s a)) \<approx> (step t a))"
            using a1 a2 a3 a4 a5 lemma_1_sub_2 by auto
           then show " ((step s a) \<approx>(sources as u (step s a)) \<approx> (step t a))"
            using a6 a7 lemma_1_sub_4 by blast
         qed
    
     
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

           have a6:"(s \<approx> (sources as u (step s a)) \<approx> t)"
            using a1 a2 a3 a4 a5 lemma_1_sub_3 by auto
           then have a7: "(s \<approx> (sources as u (step s a)) \<approx> (step s a))"
            using a1 a2 a3 a4 a5 lemma_1_sub_1 by auto
           then have a8: "(t \<approx> (sources as u (step s a)) \<approx> (step t a))"
            using a1 a2 a3 a4 a5 lemma_1_sub_2 by auto
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

     lemma lemma_3: "\<lbrakk>reachable0 s;
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

     lemma lemma_4_sub_1: "\<lbrakk>is_grant a;
                      reachable0 s;
                      grant_local_respect;
                      the (grant_dest s a) \<notin> D\<rbrakk>
                      \<Longrightarrow> (s \<approx> D \<approx> (step s a))"
       using grant_local_respect_def by force

     lemma lemma_4: "\<lbrakk>is_grant a;
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
                    (s \<approx> (sources as u s) \<approx> t)
                    \<longrightarrow> (sources as u s) = (sources as u t)"
          proof(induct as)
            case Nil then show ?case by (simp add: sources_Nil)
          next
            case (Cons b bs)
            assume p0: "\<forall>s t u.((reachable0 s) \<and> (reachable0 t) \<and> weakly_step_consistent 
                                \<and> dynamic_local_respect \<and> policy_respect \<and> (s \<approx> (sources bs u s) \<approx> t)) \<longrightarrow>
                                  (sources bs u s) = (sources bs u t)"
            then show ?case
              proof -
              {
                 fix s t u
                 assume p1: "reachable0 s"
                 assume p2: "reachable0 t"
                 assume p3: weakly_step_consistent
                 assume p4: policy_respect
                 assume p5: "(s \<approx> (sources (b # bs) u s) \<approx> t)" 
                 assume p6: "dynamic_local_respect"
                 have "sources (b # bs) u s = sources (b # bs) u t "
                   proof (cases "is_execute b")
                     assume a0: "is_execute b "
                     have a2: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                       using a0 lemma_1 p1 p2 p3 p4 p5 p6 by blast
                     have a3: "(domain s b) = (domain t b)"
                       by (simp add: domain_vpeq_lemma)
                     have a4: "interferes (the (domain s b)) s u = interferes (the (domain t b)) t u "
                       using p1 p4 p5 sources_refl by fastforce
                     have a7: "\<forall>v. v\<in>sources bs u (step s b) 
                              \<longrightarrow> interferes (the (domain s b)) s v = interferes (the (domain t b)) t v "
                       using ivpeq_def p4 p5 sources_Cons by fastforce
                     have a8: "(sources bs u (step s b)) = (sources bs u (step t b))"
                       using a2 p0 p1 p2 p3 p4 p6 reachableStep by blast
                     then show "sources (b # bs) u s = sources (b # bs) u t "
                       using a8 a3 a7 sources_Cons by auto
                     next
                       assume a0: "\<not> is_execute b "
                       have a1: "sources (b # bs) u s = sources bs u (step s b)"
                         by (simp add: a0 sources_Cons)
                       have a2: "sources (b # bs) u t = sources bs u (step t b)"
                         by (simp add: a0 sources_Cons)
                       have a3: "((step s b) \<approx> (sources bs u (step s b)) \<approx> (step t b))"
                       have a4: "(sources bs u (step s b)) = (sources bs u (step t b))"
                       
                     
               }
              then show ?thesis by blast
              qed
          qed

       }
       then show ?thesis by blast
       qed

     lemma sources_eq1: "\<lbrakk>reachable0 s;
                    reachable0 t;
                    weakly_step_consistent;
                    dynamic_local_respect;
                    policy_respect;
                    (s \<approx> (sources as u s) \<approx> t)\<rbrakk>
                    \<Longrightarrow> (sources as u s) = (sources as u t)"
       proof (induct as)                            
         case Nil show ?case                 
           by (simp add: sources_Nil)
       next                                   
         case (Cons a as)
         assume p0: "reachable0 s"
         assume p1: "reachable0 t"
         assume p2: weakly_step_consistent
         assume p3: policy_respect
         assume p4: "(s \<approx> (sources as u s) \<approx> t)" 
         assume p5: "dynamic_local_respect"
         have a0: "sources as u s = sources as u t"
           using Cons.hyps Cons.prems(1) Cons.prems(2) Cons.prems(4) Cons.prems(5) p2 p4 by blast
         have "sources (a # as) u s = sources (a # as) u t "
           proof (cases "is_execute a \<and> (\<exists>v. interferes (the (domain s a)) s v \<and> v\<in>sources as u (step s a))")
            assume a0: "is_execute a "
            assume a1: "(\<exists>v. interferes (the (domain s a)) s  v \<and> v\<in>sources as u (step s a))"  
            have a2: "(s \<approx> sources (a # as) u s \<approx> t)"
              using Cons.prems(6) by auto
            have a3: "((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
              using Cons.prems(5) a0 a2 lemma_1 p0 p1 p2 p5 by blast
            have a4: "(domain s a) = (domain t a)"
              by (simp add: domain_vpeq_lemma)
            have a5: "interferes (the (domain s a)) s u = interferes (the (domain t a)) t u "
              using a2 p0 p3 sources_refl by fastforce
            have a6: "(\<forall>v. v\<in>sources as u (step s a)) \<longrightarrow> (s \<sim> v \<sim> t) "
              using Cons.prems(6) sources_Cons by auto
            have a7: "\<forall>v. v\<in>sources as u (step s a) \<longrightarrow> interferes (the (domain s a)) s v = interferes (the (domain t a)) t v "
              using Un_iff a2 p3 sources_Cons by fastforce
            have a8: "(sources as u (step s a)) = (sources as u (step t a)) 
                \<longrightarrow>sources (a # as) u s = sources (a # as) u t  "
              using a7 a4 sources_Cons by auto
            have a9: "reachable0 (step s a)"
              using p0 reachableStep by blast
            have a10: "reachable0 (step t a)"
              using p1 reachableStep by blast
            then obtain s' where a12: "s' = step s a"
              by auto
            then obtain t' where a13: "t' = step t a"
              by auto
            then have a14: "reachable0 s'"
              by (simp add: `s' = step s a` a9)
            then have a15: "reachable0 t'"
              by (simp add: `t' = step t a` a10)
            then have a16: "s' \<approx> (sources as u s') \<approx> t' "
              using a12 a13 a3 by blast
            then have "s' = s \<and> t'=t \<longrightarrow> sources as u s' = sources as u t'"
              using Cons.hyps Cons.prems(5) a14 a15 p2 p5 a16 by blast
            then have "sources as u s' = sources as u t'"
            have a9: "(sources as u (step s a)) = (sources as u (step t a))"
                                                                                 
            
              oops

    lemma lemma_5_test: "\<lbrakk>reachable0 s;
                    reachable0 t;
                    weakly_step_consistent;
                    dynamic_local_respect;
                    policy_respect;
                    weakly_grant_step_consistent;
                    grant_local_respect\<rbrakk>
                     \<Longrightarrow>(s \<approx> (sources as u s) \<approx> t) \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
      proof -
        assume a1: "reachable0 s"
        assume a2: "reachable0 t"
        assume a3: weakly_step_consistent
        assume a4: dynamic_local_respect
        assume a5: policy_respect
        assume a6: weakly_grant_step_consistent
        assume a7: grant_local_respect
        {
          fix as u
          have "\<forall>s t. (s \<approx> (sources as u s) \<approx> t) \<longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
            proof (induct as)
              case Nil show ?case using sources_Nil by auto
            next
              case (Cons b bs)
              assume b0: "\<forall>s t. (s \<approx> (sources bs u s) \<approx> t) \<longrightarrow> ((s \<lhd> bs \<cong> t \<lhd> (ipurge bs u t) @ u))"
              show ?case
                proof -
                {
                  fix s t
                  assume c0:  " (s \<approx> (sources bs u s) \<approx> t)"
                  have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) u t @ u"
                    proof (cases "is_execute b")
                      assume d0: "is_execute b"
                      have "s \<lhd> b # bs \<cong> t \<lhd> ipurge (b # bs) u t @ u"
                        proof (cases "the (domain s b) \<in> sources (b # as) u s")
                        assume e0: "the (domain s b) \<in> sources (b # as) u s"
                        have d1:  "ipurge (b # as) u t =  b # ipurge as u (step t b)"
                    next
                      assume d0: "\<not> (is_execute b)"
         
          oops


    lemma lemma_5: "\<lbrakk>reachable0 s;
                    reachable0 t;
                    weakly_step_consistent;
                    dynamic_local_respect;
                    policy_respect;
                    weakly_grant_step_consistent;
                    grant_local_respect;
                    (s \<approx> (sources as u s) \<approx> t)\<rbrakk>
                     \<Longrightarrow> ((s \<lhd> as \<cong> t \<lhd> (ipurge as u t) @ u))"
        apply (induct as)
          using sources_Nil apply auto[1]
          apply (case_tac "is_execute a")
          apply (case_tac "the (domain s a) \<in> sources (a # as) u s")
            proof - 
              assume a1: "reachable0 s"
              assume a2: "reachable0 t"
              assume a3: weakly_step_consistent
              assume a4: dynamic_local_respect
              assume a5: policy_respect
              assume a6: "(s \<approx> (sources as u s) \<approx> t)"
              assume a7: "(s \<lhd> as \<cong> t \<lhd> ipurge as d t @ u)"
              assume a8: "s \<approx> sources (a # as) u s \<approx> t"
              assume a9: "is_execute a"
              assume a10: "the (domain s a) \<in> sources (a # as) u s"
              assume a11: "the (domain s a) \<notin> sources (a # as) u s"
              have b1: "ipurge (a # as) u t =  a # ipurge as u (step s a)"
                using a10 a11 by blast
              then have b2: "((step s a) \<approx> (sources as u (step s a)) \<approx> (step t a))"
                using a1 a2 a3 a4 a5 a8 a9 lemma_1 by blast
              then have b3: "(step s a) \<lhd> as  \<cong>  (step t a) \<lhd> ipurge as d (step t a) @ u"
                using a10 a11 by blast
              then have b4: "run (step s a) as = run s (a # as)"
                by simp
              then have b5: "run (step t a) (ipurge as d (step t a)) = run t (ipurge (a # as) u t)"
                using a10 a11 by blast
              then show "s \<lhd> a # as \<cong> t \<lhd> ipurge (a # as) u t @ u"
                using a10 a11 by blast
              
          oops

end

end