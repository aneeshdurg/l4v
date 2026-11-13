(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Schedule_R
imports ArchVSpace_R
begin

(* FIXME: review which of these are necessary/redundant and move *)
declare hoare_weak_lift_imp[wp_split del]
declare sts_rel_idle[simp]
declare objBitsT_koTypeOf[simp]
declare gq_wp[wp]
declare setQueue_obj_at[wp]
declare doMachineOp_obj_at[wp]
declare Cons_eq_tails[simp]
declare hoare_weak_lift_imp_conj[wp_split del]

(* FIXME move *)
lemmas obj_at'_conjI = obj_at_conj'

(* FIXME move *)
lemma obj_tcb_at':
  "obj_at' (\<lambda>tcb::tcb. P tcb) t s \<Longrightarrow> tcb_at' t s"
  by (clarsimp simp: obj_at'_def)

lemma findM_awesome':
  assumes x: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow>
                  corres (\<lambda>a b. if b then (\<exists>a'. a = Some a' \<and> r a' (Some x)) else a = None)
                      P (P' (x # xs))
                      ((f >>= (\<lambda>x. return (Some x))) \<sqinter> (return None)) (g x)"
  assumes y: "corres r P (P' []) f (return None)"
  assumes z: "\<And>x xs. suffix (x # xs) xs' \<Longrightarrow>
                 \<lbrace>P' (x # xs)\<rbrace> g x \<lbrace>\<lambda>rv s. \<not> rv \<longrightarrow> P' xs s\<rbrace>"
  assumes p: "suffix xs xs'"
  shows      "corres r P (P' xs) f (findM g xs)"
proof -
  have P: "f = do x \<leftarrow> (do x \<leftarrow> f; return (Some x) od) \<sqinter> return None; if x \<noteq> None then return (the x) else f od"
    apply (rule ext)
    apply (auto simp add: bind_def alternative_def return_def split_def prod_eq_iff)
    done
  have Q: "\<lbrace>P\<rbrace> (do x \<leftarrow> f; return (Some x) od) \<sqinter> return None \<lbrace>\<lambda>rv. if rv \<noteq> None then \<top> else P\<rbrace>"
    by (wp | simp)+
  show ?thesis using p
    apply (induct xs)
     apply (simp add: y del: dc_simp)
    apply (simp only: findM.simps)
    apply (subst P)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF x])
         apply assumption
        apply (rule corres_if3)
          apply (case_tac ra, clarsimp+)[1]
         apply (rule corres_trivial, clarsimp)
         apply (case_tac ra, simp_all)[1]
        apply (erule(1) meta_mp [OF _ suffix_ConsD])
       apply (rule Q)
      apply (rule hoare_post_imp [OF _ z])
       apply simp+
    done
qed

lemmas findM_awesome = findM_awesome' [OF _ _ _ suffix_order.refl]

crunch asUser
  for ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  (wp: crunch_wps)

lemma schedule_choose_new_thread_sched_act_rct[wp]:
  "\<lbrace>\<top>\<rbrace> schedule_choose_new_thread \<lbrace>\<lambda>rs s. scheduler_action s = resume_cur_thread\<rbrace>"
  unfolding schedule_choose_new_thread_def
  by wp

crunch tcbQueueAppend
  for ghost_relation_wrapper[wp]: "ghost_relation_wrapper s"

\<comment> \<open>This proof shares many similarities with the proof of @{thm tcbSchedEnqueue_corres}\<close>
lemma tcbSchedAppend_corres:
  "tcb_ptr = tcbPtr \<Longrightarrow>
   corres dc
     (in_correct_ready_q and ready_qs_distinct and st_tcb_at runnable tcb_ptr
      and pspace_aligned and pspace_distinct)
     (sym_heap_sched_pointers and valid_sched_pointers and valid_tcbs')
     (tcb_sched_action tcb_sched_append tcb_ptr) (tcbSchedAppend tcbPtr)"
  supply if_split[split del]
         heap_path_append[simp del] fun_upd_apply[simp del] distinct_append[simp del]
  apply (rule_tac Q'="st_tcb_at' runnable' tcbPtr" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  apply (rule_tac Q="tcb_at tcb_ptr" in corres_cross_add_abs_guard)
   apply (fastforce dest: st_tcb_at_tcb_at)
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (clarsimp simp: tcb_sched_action_def tcb_sched_append_def get_tcb_queue_def
                        tcbSchedAppend_def getQueue_def unless_def when_def)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac domain)
  apply (rule corres_symb_exec_l[OF _ _ thread_get_sp]; (solves wpsimp)?)
  apply (rename_tac priority)
  apply (rule corres_symb_exec_l[OF _ _ gets_sp]; (solves wpsimp)?)
  apply (rule corres_stateAssert_ignore)
   apply (fastforce intro: ksReadyQueues_asrt_cross)
  apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; wpsimp?)
  apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
   apply wpsimp
   apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (subst if_distrib[where f="set_tcb_queue domain prio" for domain prio])
  apply (rule corres_if_strong')
    subgoal
      by (fastforce dest!: state_relation_ready_queues_relation
                           in_ready_q_tcbQueued_eq[where t=tcbPtr]
                     simp: obj_at'_def opt_pred_def opt_map_def in_correct_ready_q_def
                           obj_at_def etcb_at_def etcbs_of'_def)
   apply (find_goal \<open>match conclusion in "corres _ _ _ _ (return ())" \<Rightarrow> \<open>-\<close>\<close>)
   apply (rule monadic_rewrite_corres_l[where P=P and Q=P for P, simplified])
    apply (clarsimp simp: set_tcb_queue_def)
    apply (rule monadic_rewrite_guard_imp)
     apply (rule monadic_rewrite_modify_noop)
    apply (prop_tac "(\<lambda>d p. if d = domain \<and> p = priority
                            then ready_queues s domain priority
                            else ready_queues s d p)
                     = ready_queues s")
     apply (fastforce split: if_splits)
    apply fastforce
   apply clarsimp
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ threadGet_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_r[OF _ gets_sp]; (solves wpsimp)?)

  \<comment> \<open>break off the addToBitmap\<close>
  apply (rule corres_add_noop_lhs)
  apply (rule corres_underlying_split[rotated 2,
                                      where Q="\<lambda>_. P" and P=P and Q'="\<lambda>_. P'" and P'=P' for P P'])

     apply wpsimp
    apply (wpsimp wp: hoare_vcg_if_lift hoare_vcg_ex_lift)
   apply (corres corres: addToBitmap_if_null_noop_corres)

  apply (rule corres_from_valid_det)
    apply (fastforce intro: det_wp_modify det_wp_pre simp: set_tcb_queue_def)
   apply (wpsimp simp: tcbQueueAppend_def wp: hoare_vcg_if_lift2 | drule Some_to_the)+
   apply (clarsimp simp: ex_abs_underlying_def split: if_splits)
   apply (frule state_relation_ready_queues_relation)
   apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
   apply (drule_tac x="tcbDomain tcb" in spec)
   apply (drule_tac x="tcbPriority tcb" in spec)
   subgoal by (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: obj_at'_def)

  apply (rename_tac s rv t)
  apply (clarsimp simp: state_relation_def)
  apply (intro hoare_vcg_conj_lift_pre_fix;
         (solves \<open>frule singleton_eqD, frule set_tcb_queue_projs_inv, wpsimp simp: swp_def\<close>)?)

  \<comment> \<open>ready_queues_relation\<close>
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (intro hoare_allI)
  apply (drule singleton_eqD)
  apply (drule set_tcb_queue_new_state)
  apply (wpsimp wp: threadSet_wp simp: setQueue_def tcbQueueAppend_def)
  apply normalise_obj_at'
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac s d p s' tcb' tcb)
  apply (frule_tac t=tcbPtr in pspace_relation_tcb_domain_priority)
    apply (force simp: obj_at_def)
   apply (force simp: obj_at'_def)
  apply (clarsimp split: if_splits)
  apply (cut_tac ts="ready_queues s d p" in list_queue_relation_Nil)
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (cut_tac ts="ready_queues s (tcb_domain tcb) (tcb_priority tcb)"
              in obj_at'_tcbQueueEnd_ksReadyQueues)
      apply fast
     apply fast
    apply fastforce
   apply fastforce
  apply (cut_tac xs="ready_queues s d p" in heap_path_head')
   apply (force dest!: spec simp: list_queue_relation_def)
  apply (clarsimp simp: list_queue_relation_def)

  apply (case_tac "d \<noteq> tcb_domain tcb \<or> p \<noteq> tcb_priority tcb")
   apply (cut_tac d=d and d'="tcb_domain tcb" and p=p and p'="tcb_priority tcb"
               in ready_queues_disjoint)
      apply force
     apply fastforce
    apply fastforce
   apply (prop_tac "tcbPtr \<notin> set (ready_queues s d p)")
    apply (clarsimp simp: obj_at'_def opt_pred_def opt_map_def)
    apply (metis inQ_def option.simps(5) tcb_of'_TCB)
   apply (intro conjI impI; clarsimp)

    \<comment> \<open>the ready queue was originally empty\<close>
         apply (rule heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply fastforce
        apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
       apply (rule prev_queue_head_heap_upd)
        apply (clarsimp simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              clarsimp simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: inQ_def in_opt_pred fun_upd_apply obj_at'_def split: if_splits)
     apply (clarsimp simp: fun_upd_apply split: if_splits)
    apply (clarsimp simp: fun_upd_apply split: if_splits)

   \<comment> \<open>the ready queue was not originally empty\<close>
   apply (clarsimp simp: obj_at'_def)
   apply (prop_tac "the (tcbQueueEnd (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb)))
                    \<notin> set (ready_queues s d p)")
    apply (erule orthD2)
    apply (drule_tac x="tcb_domain tcb" in spec)
    apply (drule_tac x="tcb_priority tcb" in spec)
    apply clarsimp
    apply (drule_tac x="the (tcbQueueEnd (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb)))"
                 in spec)
    subgoal by (auto simp: in_opt_pred opt_map_red)
   apply (intro conjI impI allI)
        apply (intro heap_path_heap_upd_not_in)
          apply (clarsimp simp: fun_upd_apply split: if_splits)
         apply simp
        apply fastforce
       apply (clarsimp simp: queue_end_valid_def fun_upd_apply split: if_splits)
      apply (intro prev_queue_head_heap_upd)
        apply (force simp: fun_upd_apply split: if_splits)
       apply (case_tac "ready_queues s d p";
              clarsimp simp: fun_upd_apply tcbQueueEmpty_def split: if_splits)
      apply (clarsimp simp: fun_upd_apply inQ_def split: if_splits)
      apply (case_tac "ready_queues s d p"; force simp: tcbQueueEmpty_def)
     apply (case_tac "t = tcbPtr")
      apply (clarsimp simp: inQ_def fun_upd_apply split: if_splits)
     apply (case_tac "t = the (tcbQueueEnd (ksReadyQueues s' (tcb_domain tcb, tcb_priority tcb)))")
      apply (clarsimp simp: inQ_def opt_pred_def fun_upd_apply)
     apply (clarsimp simp: inQ_def in_opt_pred opt_map_def fun_upd_apply)
    apply (clarsimp simp: fun_upd_apply split: if_splits)
   apply (clarsimp simp: fun_upd_apply split: if_splits)

  \<comment> \<open>d = tcb_domain tcb \<and> p = tcb_priority tcb\<close>
  apply clarsimp
  apply (drule_tac x="tcb_domain tcb" in spec)
  apply (drule_tac x="tcb_priority tcb" in spec)
  apply (cut_tac ts="ready_queues s (tcb_domain tcb) (tcb_priority tcb)"
              in he_ptrs_head_iff_he_ptrs_end)
   apply (force simp: list_queue_relation_def)
  apply (frule valid_tcbs'_maxDomain[where t=tcbPtr], simp add: obj_at'_def)
  apply (frule valid_tcbs'_maxPriority[where t=tcbPtr], simp add: obj_at'_def)
  apply (drule valid_sched_pointersD[where t=tcbPtr])
    apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
   apply (clarsimp simp: in_opt_pred opt_map_red obj_at'_def)
  apply (intro conjI; clarsimp)

   \<comment> \<open>the ready queue was originally empty\<close>
   apply (force simp: inQ_def in_opt_pred fun_upd_apply opt_map_def obj_at'_def
                      queue_end_valid_def prev_queue_head_def
               split: if_splits option.splits)

   \<comment> \<open>the ready queue was not originally empty\<close>
  apply (drule (2) heap_ls_append[where new=tcbPtr])
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def opt_map_def split: if_splits)
  apply (rule conjI)
   apply (clarsimp simp: fun_upd_apply queue_end_valid_def)
  apply (rule conjI)
   apply (subst opt_map_upd_triv)
    apply (clarsimp simp: opt_map_def fun_upd_apply queue_end_valid_def split: if_splits)
   apply (clarsimp simp: prev_queue_head_def fun_upd_apply split: if_splits)
  by (clarsimp simp: inQ_def in_opt_pred fun_upd_apply queue_end_valid_def split: if_splits)

lemma tcbQueueAppend_valid_objs'[wp]:
  "\<lbrace>\<lambda>s. valid_objs' s \<and> tcb_at' tcbPtr s \<and> (\<forall>end. tcbQueueEnd queue = Some end \<longrightarrow> tcb_at' end s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')
  apply (clarsimp simp: tcbQueueEmpty_def valid_bound_tcb'_def split: option.splits)
  done

lemma tcbSchedAppend_valid_objs'[wp]:
  "\<lbrace>valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def setQueue_def)
  apply (wpsimp wp: threadSet_valid_objs' threadGet_wp hoare_vcg_all_lift)
  apply (normalise_obj_at', rename_tac tcb "end")
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply clarsimp
  apply (frule he_ptrs_head_iff_he_ptrs_end)
  apply (force dest!: obj_at'_tcbQueueEnd_ksReadyQueues simp: tcbQueueEmpty_def obj_at'_def)
  done

crunch tcbSchedAppend, tcbSchedDequeue
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: threadSet_pred_tcb_no_state simp: unless_def tcb_to_itcb'_def)

crunch tcbSchedAppend, tcbSchedDequeue, tcbSchedEnqueue
  for tcb_at'[wp]: "tcb_at' t"
  and cap_to'[wp]: "ex_nonz_cap_to' p"
  and ifunsafe'[wp]: if_unsafe_then_cap'
  (wp: crunch_wps simp: crunch_simps)

lemma tcbSchedAppend_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  unfolding tcbSchedAppend_def
  apply (wpsimp wp: tcbQueueAppend_if_live_then_nonz_cap' threadGet_wp simp: bitmap_fun_defs)
  apply (frule_tac p=tcbPtr in if_live_then_nonz_capE')
   apply (fastforce simp: ko_wp_at'_def st_tcb_at'_def obj_at'_def runnable_eq_active' live'_def)
  apply (clarsimp simp: tcbQueueEmpty_def)
  apply (erule if_live_then_nonz_capE')
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def)
  apply (drule_tac x="tcbDomain tcb" in spec)
  apply (drule_tac x="tcbPriority tcb" in spec)
  apply (fastforce dest!: obj_at'_tcbQueueEnd_ksReadyQueues
                    simp: ko_wp_at'_def inQ_def obj_at'_def tcbQueueEmpty_def live'_def)
  done

lemma tcbSchedDequeue_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap' and valid_objs' and sym_heap_sched_pointers\<rbrace>
   tcbSchedDequeue tcbPtr
   \<lbrace>\<lambda>_. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wpsimp wp: tcbQueueRemove_if_live_then_nonz_cap' threadGet_wp)
  apply (fastforce elim: if_live_then_nonz_capE' simp: obj_at'_def ko_wp_at'_def live'_def)
  done


crunch tcbSchedAppend
  for idle'[wp]: valid_idle'
  (simp: unless_def crunch_simps obj_at'_def wp: getObject_tcb_wp)

lemma tcbSchedEnqueue_vms'[wp]:
  "tcbSchedEnqueue t \<lbrace>valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma tcbSchedEnqueue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedEnqueue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedEnqueue_def)
  apply (wpsimp simp: unless_def)+
  done

lemma ct_idle_or_in_cur_domain'_lift2:
  "\<lbrakk> \<And>t. \<lbrace>tcb_in_cur_domain' t\<rbrace>         f \<lbrace>\<lambda>_. tcb_in_cur_domain' t\<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksCurThread s) \<rbrace>       f \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s) \<rbrace>      f \<lbrace>\<lambda>_ s. P (ksIdleThread s) \<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (ksSchedulerAction s) \<rbrace> f \<lbrace>\<lambda>_ s. P (ksSchedulerAction s) \<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace> ct_idle_or_in_cur_domain'\<rbrace> f \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (unfold ct_idle_or_in_cur_domain'_def)
  apply (rule hoare_lift_Pf2[where f=ksCurThread])
  apply (rule hoare_lift_Pf2[where f=ksSchedulerAction])
  including no_pre
  apply (wp hoare_weak_lift_imp hoare_vcg_disj_lift)
  apply simp+
  done

lemma threadSet_mdb':
  "\<lbrace>valid_mdb' and obj_at' (\<lambda>t. \<forall>(getF, setF) \<in> ran tcb_cte_cases. getF t = getF (f t)) t\<rbrace>
   threadSet f t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (wpsimp wp: setObject_tcb_mdb' getTCB_wp simp: threadSet_def obj_at'_def)
  apply fastforce
  done

lemma tcbSchedNext_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbSchedNext_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  by (wpsimp wp: threadSet_mdb')
     (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)

lemma tcbSchedPrev_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbSchedPrev_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  by (wpsimp wp: threadSet_mdb')
     (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)

lemma tcbQueueRemove_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> valid_objs' s\<rbrace> tcbQueueRemove q tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueRemove_def
  apply (wpsimp wp: getTCB_wp)
  apply (frule (1) tcb_ko_at_valid_objs_valid_tcb')
  apply (fastforce simp: valid_tcb'_def obj_at'_def)
  done

lemma tcbQueuePrepend_valid_mdb':
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr
    and (\<lambda>s. \<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueHead queue)) s)\<rbrace>
   tcbQueuePrepend queue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueuePrepend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueueAppend_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> tcb_at' tcbPtr s
        \<and> (\<not> tcbQueueEmpty queue \<longrightarrow> tcb_at' (the (tcbQueueEnd queue)) s)\<rbrace>
   tcbQueueAppend queue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbQueueAppend_def
  by (wpsimp wp: hoare_vcg_if_lift2 hoare_vcg_imp_lift')

lemma tcbQueued_update_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and tcb_at' tcbPtr\<rbrace> threadSet (tcbQueued_update f) tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  by (wpsimp wp: threadSet_mdb')
     (fastforce simp: obj_at'_def valid_tcb'_def tcb_cte_cases_def tcb_cte_cases_neqs)

lemma valid_mdb'_ksReadyQueuesL1Bitmap_update[simp]:
  "valid_mdb' (ksReadyQueuesL1Bitmap_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma valid_mdb'_ksReadyQueuesL2Bitmap_update[simp]:
  "valid_mdb' (ksReadyQueuesL2Bitmap_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma tcbSchedEnqueue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedEnqueue tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedEnqueue_def setQueue_def)
  apply (wpsimp wp: tcbQueuePrepend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  apply normalise_obj_at'
  apply (fastforce dest!: obj_at'_tcbQueueHead_ksReadyQueues
                    simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)
  done

lemma tcbSchedEnqueue_valid_pspace'[wp]:
  "tcbSchedEnqueue tcbPtr \<lbrace>valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def
  by wpsimp

crunch tcbSchedEnqueue
  for cur_tcb'[wp]: cur_tcb'
  (wp: threadSet_cur)

lemma tcbSchedEnqueue_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   tcbSchedEnqueue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    valid_dom_schedule'_lift
                    untyped_ranges_zero_lift tcbSchedEnqueue_ct_not_inQ
              simp: cteCaps_of_def o_def)
  done

lemma tcbSchedAppend_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma tcbQueueAppend_tcbPriority_obj_at'[wp]:
  "tcbQueueAppend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def gen_objBits_simps ps_clear_def split: if_splits)

lemma tcbQueueAppend_tcbDomain_obj_at'[wp]:
  "tcbQueueAppend queue tptr \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  unfolding tcbQueueAppend_def
  apply (wpsimp wp: threadSet_wp)
  by (auto simp: obj_at'_def gen_objBits_simps ps_clear_def split: if_splits)

lemma tcbSchedAppend_tcbDomain[wp]:
  "tcbSchedAppend t \<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  by wpsimp

lemma tcbSchedAppend_tcbPriority[wp]:
  "tcbSchedAppend t \<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def)
  by wpsimp

lemma tcbSchedAppend_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedAppend t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp+
  done

crunch tcbSchedDequeue, tcbSchedAppend
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"

lemma tcbSchedAppend_sch_act_wf[wp]:
  "tcbSchedAppend thread \<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  by (wpsimp wp: sch_act_wf_lift)

lemma tcbSchedAppend_valid_bitmapQ[wp]:
  "\<lbrace>valid_bitmaps\<rbrace> tcbSchedAppend tcbPtr \<lbrace>\<lambda>_. valid_bitmapQ\<rbrace>"
  supply if_split[split del]
  unfolding tcbSchedAppend_def
  apply (wpsimp simp: tcbQueueAppend_def
                  wp: setQueue_valid_bitmapQ' addToBitmap_valid_bitmapQ_except addToBitmap_bitmapQ
                      threadGet_wp hoare_vcg_if_lift2)
  apply (clarsimp simp: ksReadyQueues_asrt_def split: if_splits)
  apply normalise_obj_at'
  apply (force dest: he_ptrs_head_iff_he_ptrs_end
               simp: valid_bitmaps_def valid_bitmapQ_def tcbQueueEmpty_def)
  done

lemma tcbSchedAppend_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_tcbs' and pspace_aligned' and pspace_distinct'\<rbrace>
   tcbSchedAppend tcbPtr
   \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (clarsimp simp: tcbSchedAppend_def setQueue_def)
  apply (wpsimp wp: tcbQueueAppend_valid_mdb' threadGet_wp simp: bitmap_fun_defs)
  apply (fastforce dest: obj_at'_tcbQueueEnd_ksReadyQueues
                   simp: ready_queue_relation_def ksReadyQueues_asrt_def obj_at'_def)
  done

lemma tcbSchedAppend_valid_bitmaps[wp]:
  "tcbSchedAppend tcbPtr \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def
  apply wpsimp
  apply (clarsimp simp: valid_bitmaps_def)
  done

locale Schedule_R =
  assumes tcbSchedAppend_state_hyp_refs_of'[wp]:
    "\<And>P t. tcbSchedAppend t \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  assumes tcbSchedDequeue_state_hyp_refs_of'[wp]:
    "\<And>P t. tcbSchedDequeue t \<lbrace>\<lambda>s. P (state_hyp_refs_of' s)\<rbrace>"
  assumes arch_switchToThread_corres_interface:
    "corres dc (valid_arch_state and valid_objs and valid_asid_map and valid_arch_caps
                and pspace_aligned and pspace_distinct and valid_global_objs
                and (\<lambda>s. sym_refs (state_hyp_refs_of s))
                and valid_vspace_objs and pspace_in_kernel_window and valid_cur_fpu and tcb_at t)
               (no_0_obj')
               (arch_switch_to_thread t) (Arch.switchToThread t)"
  assumes arch_switchToIdleThread_corres_interface:
    "corres dc
       (valid_arch_state and pspace_aligned and pspace_distinct and valid_asid_map and valid_idle
        and valid_arch_caps and valid_global_objs and valid_vspace_objs and valid_objs)
       (no_0_obj')
       arch_switch_to_idle_thread Arch.switchToIdleThread"
  assumes arch_switch_to_thread_ready_queues[wp]:
    "\<And>t P. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. P (ready_queues s)\<rbrace>"
  assumes arch_switch_to_thread_pspace_aligned[wp]:
    "\<And>t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. pspace_aligned s\<rbrace>"
  assumes arch_switch_to_thread_pspace_distinct[wp]:
    "\<And>t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. pspace_distinct s\<rbrace>"
  assumes arch_switch_to_idle_thread_pspace_aligned[wp]:
    "arch_switch_to_idle_thread \<lbrace>\<lambda>s::det_state. pspace_aligned s\<rbrace>"
  assumes arch_switch_to_idle_thread_pspace_distinct[wp]:
    "arch_switch_to_idle_thread \<lbrace>\<lambda>s::det_state. pspace_distinct s\<rbrace>"
  assumes arch_switch_to_thread_valid_idle[wp]:
    "\<And>t. arch_switch_to_thread t \<lbrace>\<lambda>s::det_state. valid_idle s\<rbrace>"
  assumes Arch_switchToThread_sym_heap_sched_pointers[wp]:
    "\<And>t. Arch.switchToThread t \<lbrace>sym_heap_sched_pointers\<rbrace>"
  assumes Arch_switchToThread_valid_objs'[wp]:
    "\<And>t. Arch.switchToThread t \<lbrace>valid_objs'\<rbrace>"
  assumes Arch_switchToThread_invs[wp]:
    "\<And>t. \<lbrace>invs' and tcb_at' t\<rbrace> Arch.switchToThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  assumes Arch_switchToThread_invs_no_cicd'[wp]:
    "\<And>t. Arch.switchToThread t \<lbrace>invs_no_cicd'\<rbrace>"
  assumes Arch_switchToThread_ksCurDomain[wp]:
    "\<And>t P. Arch.switchToThread t \<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>"
  assumes Arch_switchToThread_tcbDomain[wp]:
    "\<And>t P t'. Arch.switchToThread t \<lbrace> obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t'\<rbrace>"
  assumes Arch_switchToThread_tcbState[wp]:
    "\<And>t P t'. Arch.switchToThread t \<lbrace> obj_at' (\<lambda>tcb. P (tcbState tcb)) t'\<rbrace>"
  (* can't interface pred_tcb_at' due to free variable in projection *)
  assumes Arch_switchToThread_st_tcb_at'[wp]:
    "\<And>t P t'. Arch.switchToThread t \<lbrace> st_tcb_at' P t'\<rbrace>"
  assumes Arch_switchToThread_it[wp]:
    "\<And>t P. Arch.switchToThread t \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  assumes Arch_switchToIdleThread_it[wp]:
    "\<And>P. Arch.switchToIdleThread \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace>"
  assumes Arch_switchToIdleThread_not_queued'[wp]:
    "\<And>t. Arch.switchToIdleThread \<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  assumes Arch_switchToIdleThread_tcbState[wp]:
    "\<And>P t. Arch.switchToIdleThread \<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace>"
  assumes Arch_switchToIdleThread_invs_no_cicd':
    "Arch.switchToIdleThread \<lbrace>invs_no_cicd'\<rbrace> "
  assumes bitmapQ_lookupBitmapPriority_simp:
    "\<And>s d.
     \<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0 ; valid_bitmapQ s ; bitmapQ_no_L1_orphans s \<rbrakk> \<Longrightarrow>
     bitmapQ d (lookupBitmapPriority d s) s =
      (ksReadyQueuesL1Bitmap s d !! word_log2 (ksReadyQueuesL1Bitmap s d) \<and>
       ksReadyQueuesL2Bitmap s (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d))) !!
         word_log2 (ksReadyQueuesL2Bitmap s
                      (d, invertL1Index (word_log2 (ksReadyQueuesL1Bitmap s d)))))"
begin

crunch switchToThread, switchToIdleThread
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

lemma tcbSchedAppend_invs'[wp]:
  "\<lbrace>invs' and (\<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow> ksCurThread s \<noteq> t)\<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift tcbSchedAppend_ct_not_inQ
                    ct_idle_or_in_cur_domain'_lift2 cur_tcb_lift valid_dom_schedule'_lift
              simp: cteCaps_of_def o_def)
  done

lemma tcbSchedAppend_all_invs_but_ct_not_inQ':
  "\<lbrace>invs'\<rbrace>
   tcbSchedAppend t
   \<lbrace>\<lambda>_. all_invs_but_ct_not_inQ'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift tcbSchedAppend_ct_not_inQ
                    ct_idle_or_in_cur_domain'_lift2 cur_tcb_lift valid_dom_schedule'_lift
              simp: cteCaps_of_def o_def)
  done

lemma tcbSchedAppend_invs'_not_ResumeCurrentThread:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread)\<rbrace>
     tcbSchedAppend t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by wpsimp

end (* Schedule_R *)

lemma tcbSchedEnqueue_invs'_not_ResumeCurrentThread:
  "\<lbrace>invs'
    and st_tcb_at' runnable' t
    and (\<lambda>s. ksSchedulerAction s \<noteq> ResumeCurrentThread)\<rbrace>
     tcbSchedEnqueue t
   \<lbrace>\<lambda>_. invs'\<rbrace>"
  by wpsimp

lemma tcb_at'_has_tcbDomain:
 "tcb_at' t s \<Longrightarrow> \<exists>p. obj_at' (\<lambda>tcb. tcbDomain tcb = p) t s"
 by (clarsimp simp add: obj_at'_def)

lemma tcbSchedDequeue_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift)
  done

lemma tcbSchedDequeue_tcb_in_cur_domain'[wp]:
  "\<lbrace>tcb_in_cur_domain' t'\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. tcb_in_cur_domain' t' \<rbrace>"
  apply (rule tcb_in_cur_domain'_lift)
   apply wp
  apply (clarsimp simp: tcbSchedDequeue_def tcbQueueRemove_def)
  apply (wpsimp wp: hoare_when_weak_wp getObject_tcb_wp threadGet_wp)
  done

lemma tcbSchedDequeue_valid_mdb'[wp]:
  "\<lbrace>valid_mdb' and valid_objs'\<rbrace> tcbSchedDequeue tcbPtr \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding tcbSchedDequeue_def
  apply (wpsimp simp: bitmap_fun_defs setQueue_def wp: threadSet_mdb' tcbQueueRemove_valid_mdb')
      apply (rule_tac Q'="\<lambda>_. tcb_at' tcbPtr" in hoare_post_imp)
       apply (fastforce simp: tcb_cte_cases_def tcb_cte_cases_neqs)
      apply (wpsimp wp: threadGet_wp)+
  apply (fastforce simp: obj_at'_def)
  done

lemma ready_qs_runnable_cross:
  "\<lbrakk>(s, s') \<in> state_relation; pspace_aligned s; pspace_distinct s; valid_queues s\<rbrakk>
   \<Longrightarrow> ready_qs_runnable s'"
  apply (clarsimp simp: ready_qs_runnable_def)
  apply normalise_obj_at'
  apply (frule state_relation_ready_queues_relation)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x="tcbDomain ko" in spec)
  apply (drule_tac x="tcbPriority ko" in spec)
  apply clarsimp
  apply (drule_tac x=t in bspec)
   apply (fastforce simp: inQ_def in_opt_pred obj_at'_def opt_map_red)
  apply (fastforce dest: st_tcb_at_runnable_cross simp: obj_at'_def st_tcb_at'_def)
  done

method add_ready_qs_runnable =
  rule_tac Q'=ready_qs_runnable in corres_cross_add_guard,
  (clarsimp simp: pred_conj_def)?,
  (frule valid_sched_valid_queues)?, (frule invs_psp_aligned)?, (frule invs_distinct)?,
  fastforce dest: ready_qs_runnable_cross

defs idleThreadNotQueued_def:
  "idleThreadNotQueued s \<equiv> obj_at' (Not \<circ> tcbQueued) (ksIdleThread s) s"

lemma idle_thread_not_queued:
  "\<lbrakk>valid_idle s; valid_queues s\<rbrakk>
   \<Longrightarrow> \<not> (\<exists>d p. idle_thread s \<in> set (ready_queues s d p))"
  apply (clarsimp simp: valid_queues_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (drule_tac x="idle_thread s" in bspec)
   apply fastforce
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma valid_idle_tcb_at:
  "valid_idle s \<Longrightarrow> tcb_at (idle_thread s) s"
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_tcb_def)

lemma setCurThread_corres:
  "corres dc (valid_idle and valid_queues and pspace_aligned and pspace_distinct) \<top>
     (modify (cur_thread_update (\<lambda>_. t))) (setCurThread t)"
  apply (clarsimp simp: setCurThread_def)
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (clarsimp simp: idleThreadNotQueued_def)
   apply (frule (1) idle_thread_not_queued)
   apply (frule state_relation_pspace_relation)
   apply (frule state_relation_ready_queues_relation)
   apply (frule state_relation_idle_thread)
   apply (frule valid_idle_tcb_at)
   apply (frule (3) tcb_at_cross)
   apply (fastforce dest!: in_ready_q_tcbQueued_eq[THEN arg_cong_Not, THEN iffD1]
                     simp: obj_at'_def opt_pred_def opt_map_def)
  apply (rule corres_modify)
  apply (simp add: state_relation_def swp_def)
  done

lemma (in Schedule_R) tcbSchedDequeue_invs'[wp]:
  "tcbSchedDequeue t \<lbrace>invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: valid_irq_node_lift valid_irq_handlers_lift'' irqs_masked_lift
                    untyped_ranges_zero_lift ct_idle_or_in_cur_domain'_lift2 cur_tcb_lift
                    valid_dom_schedule'_lift
              simp: cteCaps_of_def o_def)
  done

lemma valid_queues_in_correct_ready_q[elim!]:
  "valid_queues s \<Longrightarrow> in_correct_ready_q s"
  by (clarsimp simp: valid_queues_def in_correct_ready_q_def)

lemma valid_queues_ready_qs_distinct[elim!]:
  "valid_queues s \<Longrightarrow> ready_qs_distinct s"
  by (clarsimp simp: valid_queues_def ready_qs_distinct_def)

context Schedule_R begin

lemmas arch_switch_to_thread_ready_qs_distinct[wp] =
  ready_qs_distinct_lift[OF arch_switch_to_thread_ready_queues]

(* AARCH64/RISCV64 does not need valid_asid_map here, but we propagate it due to generic interface *)
lemma switchToThread_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_arch_caps and valid_global_objs and pspace_in_kernel_window
                and st_tcb_at runnable t and (\<lambda>s. sym_refs (state_hyp_refs_of s))
                and valid_queues and valid_idle and valid_cur_fpu)
             (no_0_obj' and sym_heap_sched_pointers and valid_objs')
             (switch_to_thread t) (switchToThread t)"
  apply (rule_tac Q'="st_tcb_at' runnable' t" in corres_cross_add_guard)
   apply (fastforce intro!: st_tcb_at_runnable_cross simp: obj_at_def is_tcb_def)
  apply add_ready_qs_runnable
  apply (simp add: switch_to_thread_def Thread_H.switchToThread_def)
  apply (rule corres_symb_exec_l[OF _ _ get_sp]; (solves wpsimp)?)
  apply (rule corres_symb_exec_l[OF _ _ assert_sp]; (solves wpsimp)?)
    apply (rule corres_symb_exec_r[OF _ isRunnable_sp]; (solves wpsimp)?)
    apply (rule corres_symb_exec_r[OF _ assert_sp, rotated]; (solves wpsimp)?)
     apply wpsimp
     apply (fastforce simp: st_tcb_at'_def runnable_eq_active' obj_at'_def)
    apply (rule corres_stateAssert_ignore)
     apply (fastforce dest!: state_relation_ready_queues_relation intro: ksReadyQueues_asrt_cross)
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply fastforce
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF arch_switchToThread_corres_interface])
        apply (rule corres_split[OF tcbSchedDequeue_corres setCurThread_corres])
          apply (wpsimp simp: is_tcb_def wp: in_correct_ready_q_lift)+
     apply (fastforce intro!: st_tcb_at_tcb_at)
    apply wpsimp
   apply wpsimp
   apply (fastforce dest!: st_tcb_at_tcb_at simp: tcb_at_def)
  apply wpsimp
  apply (fastforce dest!: st_tcb_at_tcb_at simp: tcb_at_def)
  done

lemma switchToIdleThread_corres:
  "corres dc
     (invs and valid_queues)
     invs_no_cicd'
     switch_to_idle_thread switchToIdleThread"
  unfolding switch_to_idle_thread_def Thread_H.switchToIdleThread_def
  apply add_ready_qs_runnable
  apply (rule corres_stateAssert_ignore, fastforce)
  apply (corres corres: getIdleThread_corres arch_switchToIdleThread_corres_interface
                        setCurThread_corres[@lift_corres_args])
      apply (wpsimp simp: state_relation_def cdt_relation_def)
   apply fastforce
  apply (fastforce simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_pspace'_def)
  done

end (* Schedule_R *)

lemma tcb_at_idle_thread_lift:
  assumes T: "\<And>T' t. \<lbrace>typ_at T' t\<rbrace> f \<lbrace>\<lambda>rv. typ_at T' t\<rbrace>"
  assumes I: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. tcb_at (idle_thread s) s \<rbrace> f \<lbrace>\<lambda>rv s. tcb_at (idle_thread s) s\<rbrace>"
  apply (simp add: tcb_at_typ)
  apply (rule hoare_lift_Pf[where f=idle_thread])
  by (wpsimp wp: T I)+

lemma tcb_at'_ksIdleThread_lift:
  assumes T: "\<And>T' t. \<lbrace>typ_at' T' t\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T' t\<rbrace>"
  assumes I: "\<And>P. \<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. tcb_at' (ksIdleThread s) s \<rbrace> f \<lbrace>\<lambda>rv s. tcb_at' (ksIdleThread s) s\<rbrace>"
  apply (simp add: tcb_at_typ_at')
  apply (rule hoare_lift_Pf[where f=ksIdleThread])
  by (wpsimp wp: T I)+

lemma gq_sp: "\<lbrace>P\<rbrace> getQueue d p \<lbrace>\<lambda>rv. P and (\<lambda>s. ksReadyQueues s (d, p) = rv)\<rbrace>"
  by (unfold getQueue_def, rule gets_sp)

lemma sch_act_wf:
  "sch_act_wf sa s = ((\<forall>t. sa = SwitchToThread t \<longrightarrow> st_tcb_at' runnable' t s \<and>
                                                    tcb_in_cur_domain' t s) \<and>
                      (sa = ResumeCurrentThread \<longrightarrow> ct_in_state' activatable' s))"
  by (case_tac sa,  simp_all add: )

lemma setCurThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and st_tcb_at' activatable' t and obj_at' (\<lambda>x. \<not> tcbQueued x) t and tcb_in_cur_domain' t\<rbrace>
     setCurThread t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
proof -
  have ct_not_inQ_ct: "\<And>s t . \<lbrakk> ct_not_inQ s; obj_at' (\<lambda>x. \<not> tcbQueued x) t s\<rbrakk> \<Longrightarrow> ct_not_inQ (s\<lparr> ksCurThread := t \<rparr>)"
    apply (simp add: ct_not_inQ_def o_def)
    done
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (clarsimp simp add: all_invs_but_ct_idle_or_in_cur_domain'_def invs'_def cur_tcb'_def
                              valid_state'_def sch_act_wf ct_in_state'_def state_refs_of'_def
                              ps_clear_def valid_irq_node'_def ct_not_inQ_ct
                              ct_idle_or_in_cur_domain'_def bitmapQ_defs valid_bitmaps_def
                        cong: option.case_cong)
    done
qed

(* Don't use this rule when considering the idle thread. The invariant ct_idle_or_in_cur_domain'
   says that either "tcb_in_cur_domain' t" or "t = ksIdleThread s".
   Use setCurThread_invs_idle_thread instead. *)
lemma setCurThread_invs:
  "\<lbrace>invs' and st_tcb_at' activatable' t and obj_at' (\<lambda>x. \<not> tcbQueued x) t and
    tcb_in_cur_domain' t\<rbrace> setCurThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_pre, rule setCurThread_invs_no_cicd')
     (simp add: invs'_to_invs_no_cicd'_def)

lemma setCurThread_invs_no_cicd'_idle_thread:
  "\<lbrace>invs_no_cicd' and (\<lambda>s. t = ksIdleThread s) \<rbrace> setCurThread t \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def invs'_def cur_tcb'_def
                        valid_state'_def valid_idle'_def
                        sch_act_wf ct_in_state'_def state_refs_of'_def
                        ps_clear_def valid_irq_node'_def
                        ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                        valid_queues_def bitmapQ_defs valid_bitmaps_def pred_tcb_at'_def
                  cong: option.case_cong)
  apply (clarsimp simp: idle_tcb'_def ct_not_inQ_def ps_clear_def obj_at'_def st_tcb_at'_def
                        idleThreadNotQueued_def)
  done

lemma setCurThread_invs_idle_thread:
  "\<lbrace>invs' and (\<lambda>s. t = ksIdleThread s) \<rbrace> setCurThread t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (rule hoare_pre, rule setCurThread_invs_no_cicd'_idle_thread)
     (clarsimp simp: invs'_to_invs_no_cicd'_def all_invs_but_ct_idle_or_in_cur_domain'_def)

lemma tcbSchedDequeue_not_tcbQueued:
  "\<lbrace>\<top>\<rbrace> tcbSchedDequeue t \<lbrace>\<lambda>_. obj_at' (\<lambda>x. \<not> tcbQueued x) t\<rbrace>"
  apply (simp add: tcbSchedDequeue_def)
  apply (wp|clarsimp)+
  apply (rule_tac Q'="\<lambda>queued. obj_at' (\<lambda>x. tcbQueued x = queued) t" in hoare_post_imp)
     apply (clarsimp simp: obj_at'_def)
    apply (wpsimp wp: threadGet_wp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma asUser_obj_at[wp]:
  "asUser t' f \<lbrace>\<lambda>s. P' (obj_at' (P \<circ> tcbState) t s)\<rbrace>"
  apply (wpsimp simp: asUser_def threadGet_stateAssert_gets_asUser wp: threadSet_obj_at'_no_state)
  apply (simp add: obj_at'_def)
  done

crunch asUser
  for valid_arch_state'[wp]: "valid_arch_state'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_irq_states'[wp]: "valid_irq_states'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_machine_state'[wp]: "valid_machine_state'"
(wp: crunch_wps simp: crunch_simps)

lemma asUser_valid_irq_node'[wp]:
  "asUser t (setRegister f r) \<lbrace>\<lambda>s. valid_irq_node' (irq_node' s) s\<rbrace>"
  apply (rule_tac valid_irq_node_lift)
   apply (simp add: asUser_def)
   apply (wpsimp wp: crunch_wps)+
  done

crunch asUser
  for irq_masked'_helper: "\<lambda>s. P (intStateIRQTable (ksInterruptState s))"
(wp: crunch_wps simp: crunch_simps)

lemma asUser_irq_masked'[wp]:
  "\<lbrace>irqs_masked'\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ . irqs_masked'\<rbrace>"
  apply (rule irqs_masked_lift)
  apply (rule asUser_irq_masked'_helper)
  done

lemma asUser_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> asUser t (setRegister f r)
          \<lbrace>\<lambda>_ . ct_not_inQ\<rbrace>"
  apply (clarsimp simp: submonad_asUser.fn_is_sm submonad_fn_def)
  apply (rule bind_wp)+
     prefer 4
     apply (rule stateAssert_sp)
    prefer 3
    apply (rule gets_inv)
   defer
   apply (rule select_f_inv)
  apply (case_tac rv; simp)
  apply (clarsimp simp: asUser_replace_def obj_at'_def fun_upd_def
                  split: option.split kernel_object.split)
  apply wp
  apply (clarsimp simp: ct_not_inQ_def obj_at'_def objBitsKO_def ps_clear_def dom_def)
  apply (rule conjI; clarsimp; blast)
  done

crunch asUser
  for pspace_domain_valid[wp]: "pspace_domain_valid"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for valid_dom_schedule'[wp]: "valid_dom_schedule'"
(wp: crunch_wps simp: crunch_simps)

crunch asUser
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: crunch_wps simp: unless_def)

crunch asUser
  for ctes_of[wp]: "\<lambda>s. P (ctes_of s)"
  (wp: crunch_wps simp: unless_def)

lemmas asUser_cteCaps_of[wp] = cteCaps_of_ctes_of_lift[OF asUser_ctes_of]

lemma asUser_utr[wp]:
  "\<lbrace>untyped_ranges_zero'\<rbrace> asUser f t \<lbrace>\<lambda>_. untyped_ranges_zero'\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (rule hoare_pre, wp untyped_ranges_zero_lift)
  apply (simp add: o_def)
  done

lemma setCurThread_ct_in_state:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace> setCurThread t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  by (wpsimp simp: setCurThread_def)
     (simp add: ct_in_state'_def pred_tcb_at'_def o_def)

lemma threadSet_timeslice_invs:
  "\<lbrace>invs' and tcb_at' t\<rbrace> threadSet (tcbTimeSlice_update b) t \<lbrace>\<lambda>rv. invs'\<rbrace>"
  by (wp threadSet_invs_trivial, simp_all add: inQ_def cong: conj_cong)

context Schedule_R begin

lemma switchToIdleThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding switchToIdleThread_def
  by (wpsimp wp: setCurThread_invs_no_cicd'_idle_thread Arch_switchToIdleThread_invs_no_cicd')

lemma switchToIdleThread_activatable_2[wp]:
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv. ct_in_state' activatable'\<rbrace>"
  unfolding switchToIdleThread_def
  by (wpsimp wp: setCurThread_ct_in_state)
     (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_idle'_def
                     pred_tcb_at'_def obj_at'_def idle_tcb'_def)

lemma Arch_switchToThread_tcb_in_cur_domain'[wp]:
  "Arch.switchToThread t \<lbrace>tcb_in_cur_domain' t'\<rbrace>"
  by (wp tcb_in_cur_domain'_lift)

lemma tcbSchedDequeue_invs_no_cicd'[wp]:
  "tcbSchedDequeue t \<lbrace>invs_no_cicd'\<rbrace>"
  unfolding all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_pspace'_def
  apply (wp tcbSchedDequeue_ct_not_inQ sch_act_wf_lift valid_irq_node_lift irqs_masked_lift
            valid_irq_handlers_lift' cur_tcb_lift ct_idle_or_in_cur_domain'_lift2
            untyped_ranges_zero_lift valid_dom_schedule'_lift
        | simp add: cteCaps_of_def o_def)+
  done

lemma switchToThread_invs_no_cicd':
  "\<lbrace>invs_no_cicd' and tcb_in_cur_domain' t \<rbrace> ThreadDecls_H.switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp setCurThread_invs_no_cicd' tcbSchedDequeue_not_tcbQueued
            Arch_switchToThread_invs_no_cicd')
  apply (auto elim!: pred_tcb'_weakenE)
  done

lemma switchToThread_invs[wp]:
  "\<lbrace>invs' and tcb_in_cur_domain' t \<rbrace> switchToThread t \<lbrace>\<lambda>rv. invs' \<rbrace>"
  apply (simp add: Thread_H.switchToThread_def )
  apply (wp threadSet_timeslice_invs setCurThread_invs
             Arch_switchToThread_invs dmo_invs'
             doMachineOp_obj_at tcbSchedDequeue_not_tcbQueued)
  by (auto elim!: pred_tcb'_weakenE)

lemma switchToThread_ct_in_state[wp]:
  "\<lbrace>obj_at' (P \<circ> tcbState) t\<rbrace> switchToThread t \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  unfolding Thread_H.switchToThread_def tcbSchedEnqueue_def unless_def
  by (wpsimp wp: setCurThread_ct_in_state simp: o_def)

end (* Schedule_R *)

lemma setCurThread_obj_at[wp]:
  "\<lbrace>obj_at' P addr\<rbrace> setCurThread t \<lbrace>\<lambda>rv. obj_at' P addr\<rbrace>"
  apply (simp add: setCurThread_def)
  apply wp
  apply (fastforce intro: obj_at'_pspaceI)
  done

lemma dmo_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace>
     doMachineOp m
   \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  by (wp ex_nonz_cap_to_pres')

lemma sct_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setCurThread t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: setCurThread_def)
  apply (wpsimp wp: ex_nonz_cap_to_pres')
  done

lemma no_longer_inQ[simp]:
  "\<not> inQ d p (tcbQueued_update (\<lambda>x. False) tcb)"
  by (simp add: inQ_def)

lemma iflive_inQ_nonz_cap_strg:
  "if_live_then_nonz_cap' s \<and> obj_at' (inQ d prio) t s
          \<longrightarrow> ex_nonz_cap_to' t s"
  by (clarsimp simp: obj_at'_real_def inQ_def live'_def
              elim!: if_live_then_nonz_capE' ko_wp_at'_weakenE)

lemmas iflive_inQ_nonz_cap[elim]
    = mp [OF iflive_inQ_nonz_cap_strg, OF conjI[rotated]]

lemma setThreadState_rct:
  "\<lbrace>\<lambda>s. (runnable' st \<or> ksCurThread s \<noteq> t)
        \<and> ksSchedulerAction s = ResumeCurrentThread\<rbrace>
   setThreadState st t
   \<lbrace>\<lambda>_ s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  apply (simp add: setThreadState_def)
  apply (rule hoare_pre_disj')
   apply (rule bind_wp [OF _
                 hoare_vcg_conj_lift
                   [OF threadSet_tcbState_st_tcb_at' [where P=runnable']
                       threadSet_nosch]])
   apply (rule bind_wp [OF _
                 hoare_vcg_conj_lift [OF isRunnable_const isRunnable_inv]])
   apply (clarsimp simp: when_def)
   apply (case_tac rv)
    apply (clarsimp, wp)[1]
   apply (clarsimp)
  apply (rule bind_wp [OF _
                hoare_vcg_conj_lift
                  [OF threadSet_ct threadSet_nosch]])
  apply (rule bind_wp [OF _ isRunnable_inv])
  apply (rule bind_wp [OF _
                hoare_vcg_conj_lift
                  [OF gct_wp gct_wp]])
  apply (rename_tac ct)
  apply (case_tac "ct\<noteq>t")
   apply (clarsimp simp: when_def)
   apply (wp)[1]
  apply (clarsimp)
  done

context Schedule_R begin

lemma bitmapQ_from_bitmap_lookup:
  "\<lbrakk> ksReadyQueuesL1Bitmap s d \<noteq> 0; valid_bitmapQ s; bitmapQ_no_L1_orphans s \<rbrakk>
   \<Longrightarrow> bitmapQ d (lookupBitmapPriority d s) s"
  apply (simp add: bitmapQ_lookupBitmapPriority_simp)
  apply (drule bit_word_log2)
  apply (drule (1) bitmapQ_no_L1_orphansD)
  apply (fastforce dest!: bit_word_log2 simp: word_ao_dist)
  done

lemma lookupBitmapPriority_obj_at':
  "\<lbrakk>ksReadyQueuesL1Bitmap s d \<noteq> 0; valid_bitmapQ s; bitmapQ_no_L1_orphans s;
    ksReadyQueues_asrt s; ready_qs_runnable s; pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> obj_at' (inQ d (lookupBitmapPriority d s) and runnable' \<circ> tcbState)
               (the (tcbQueueHead (ksReadyQueues s (d, lookupBitmapPriority d s)))) s"
  apply (drule (2) bitmapQ_from_bitmap_lookup)
  apply (simp add: valid_bitmapQ_bitmapQ_simp)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def tcbQueueEmpty_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x="lookupBitmapPriority d s" in spec)
  apply clarsimp
  apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
  apply (fastforce simp: obj_at'_and ready_qs_runnable_def obj_at'_def st_tcb_at'_def inQ_def
                         tcbQueueEmpty_def)
  done

lemma bitmapL1_zero_ksReadyQueues:
  "\<lbrakk> valid_bitmapQ s; bitmapQ_no_L1_orphans s \<rbrakk>
   \<Longrightarrow> (ksReadyQueuesL1Bitmap s d = 0) = (\<forall>p. tcbQueueEmpty (ksReadyQueues s (d, p)))"
  apply (cases "ksReadyQueuesL1Bitmap s d = 0")
   apply (force simp add: bitmapQ_def valid_bitmapQ_def)
  apply (fastforce dest: bitmapQ_from_bitmap_lookup simp: valid_bitmapQ_bitmapQ_simp)
  done

end (* Schedule_R *)

lemma prioToL1Index_le_mask:
  "\<lbrakk> prioToL1Index p = prioToL1Index p' ; p && mask wordRadix \<le> p' && mask wordRadix \<rbrakk>
   \<Longrightarrow> p \<le> p'"
  unfolding prioToL1Index_def
  apply (simp add: wordRadix_def word_le_nat_alt[symmetric])
  apply (drule shiftr_eq_neg_mask_eq)
  apply (metis add.commute word_and_le2 word_plus_and_or_coroll2 word_plus_mono_left)
  done

lemma prioToL1Index_le_index:
  "\<lbrakk> prioToL1Index p \<le> prioToL1Index p' ; prioToL1Index p \<noteq> prioToL1Index p' \<rbrakk>
   \<Longrightarrow> p \<le> p'"
  unfolding prioToL1Index_def
  apply (simp add: wordRadix_def word_le_nat_alt[symmetric])
  apply (erule (1) le_shiftr')
  done

lemma bitmapQ_ksReadyQueuesI:
  "\<lbrakk> bitmapQ d p s ; valid_bitmapQ s \<rbrakk> \<Longrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d, p))"
  unfolding valid_bitmapQ_def by simp

lemma getReadyQueuesL2Bitmap_inv[wp]:
  "\<lbrace> P \<rbrace> getReadyQueuesL2Bitmap d i \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding getReadyQueuesL2Bitmap_def by wp

lemma (in Schedule_R) switchToThread_lookupBitmapPriority_wp:
  "\<lbrace>\<lambda>s. invs_no_cicd' s \<and> bitmapQ (ksCurDomain s) (lookupBitmapPriority (ksCurDomain s) s) s \<and>
        t = the (tcbQueueHead (ksReadyQueues s (ksCurDomain s, lookupBitmapPriority (ksCurDomain s) s)))\<rbrace>
   ThreadDecls_H.switchToThread t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp setCurThread_invs_no_cicd' tcbSchedDequeue_not_tcbQueued
            Arch_switchToThread_invs_no_cicd')
  apply (auto elim!: pred_tcb'_weakenE)
  apply (prop_tac "valid_bitmapQ s")
   apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_bitmaps_def)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def valid_bitmapQ_bitmapQ_simp)
  apply (drule_tac x="ksCurDomain s" in spec)
  apply (drule_tac x="lookupBitmapPriority (ksCurDomain s) s" in spec)
  apply (clarsimp simp: all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def)
  apply (frule (3) obj_at'_tcbQueueHead_ksReadyQueues)
  apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def tcbQueueEmpty_def inQ_def)
  done

lemma setCurThread_const:
  "\<lbrace>\<lambda>_. P t \<rbrace> setCurThread t \<lbrace>\<lambda>_ s. P (ksCurThread s) \<rbrace>"
  by (simp add: setCurThread_def | wp)+

lemma oqueueEntry_inv[wp]:
  "\<lbrace>P\<rbrace> oqueueEntry t \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: oqueueEntry_def)

lemma mapM_inv_post:
  "\<lbrakk>\<And>x. \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>_. P\<rbrace>; \<And>rv s. P s \<Longrightarrow> Q rv s\<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> mapM f xs \<lbrace>Q\<rbrace>"
  by (rule hoare_strengthen_post[OF mapM_wp_inv]; assumption)

lemma oqueue_result_inv:
  "\<lbrace>P\<rbrace> (case (x :: ('a \<times> 'b) option) of None \<Rightarrow> haskell_fail []
                                        | Some (thread, _) \<Rightarrow> return thread)
   \<lbrace>\<lambda>_. P\<rbrace>"
  apply (cases x)
   apply clarsimp
  apply (case_tac a, clarsimp?, wp?)
  done

lemma oqueueSelect_inv[wp]:
  "\<lbrace>P\<rbrace> oqueueSelect q \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding oqueueSelect_def
  apply (rule hoare_pre)
   apply (wp mapM_inv_post oqueue_result_inv)
  apply (rule get_wp)
  apply simp
  done

text \<open>
  The selector only reads the state, so any property that holds for every thread also holds
  for the thread it returns.
\<close>
lemma oqueueSelect_all_wp[wp]:
  "\<lbrace>\<lambda>s. \<forall>t. Q t s\<rbrace> oqueueSelect q \<lbrace>Q\<rbrace>"
  by (rule hoare_strengthen_post[where Q'="\<lambda>_ s. \<forall>t. Q t s"], rule oqueueSelect_inv, simp)

lemma list_queue_relation_unique:
  "\<lbrakk>list_queue_relation ts q n p; list_queue_relation ts' q n p\<rbrakk> \<Longrightarrow> ts = ts'"
  by (fastforce simp: list_queue_relation_def dest: heap_ls_unique)

lemma oqueueQueueList_eq:
  "list_queue_relation ts queue (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
   \<Longrightarrow> oqueueQueueList s queue = ts"
  unfolding oqueueQueueList_def
  by (fastforce intro: some_equality dest: list_queue_relation_unique)

definition oqueue_entry_abs ::
  "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> ticks) option"
where
  "oqueue_entry_abs s t \<equiv> map_option (Pair t) (oqueue_remaining_budget s t)"

lemma oqueuePick_None_left[simp]: "oqueuePick None e = e"
  by (cases e; auto simp: oqueuePick_def split: prod.splits)

lemma oqueuePick_None_right[simp]: "oqueuePick b None = b"
  by (simp add: oqueuePick_def)

text \<open>Taking the first minimum is associative.\<close>
lemma oqueuePick_assoc:
  "oqueuePick (oqueuePick a (Some e)) (Some m) = oqueuePick a (oqueuePick (Some e) (Some m))"
  by (cases a; cases e; cases m;
      auto simp: oqueuePick_def not_less split: if_splits intro: order_trans less_le_trans le_less_trans)

lemma oqueuePick_Some_Some:
  "\<exists>z. oqueuePick (Some x) (Some m) = Some z"
  by (cases x; cases m; auto simp: oqueuePick_def split: if_splits)

text \<open>
  The Haskell selector is a left fold that keeps the earlier entry on ties. Folding from an
  accumulator is the same as folding from nothing and then comparing against the accumulator.
\<close>
lemma foldl_oqueuePick_acc:
  "foldl oqueuePick acc es =
   (case foldl oqueuePick None es of None \<Rightarrow> acc | Some m \<Rightarrow> oqueuePick acc (Some m))"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons e es)
  have lhs: "foldl oqueuePick acc (e # es) =
             (case foldl oqueuePick None es of None \<Rightarrow> oqueuePick acc e
              | Some m \<Rightarrow> oqueuePick (oqueuePick acc e) (Some m))"
    by (simp only: foldl_Cons Cons.IH[of "oqueuePick acc e"])
  have rhs: "foldl oqueuePick None (e # es) =
             (case foldl oqueuePick None es of None \<Rightarrow> e | Some m \<Rightarrow> oqueuePick e (Some m))"
    by (simp only: foldl_Cons oqueuePick_None_left Cons.IH[of e])
  show ?case
  proof (cases e)
    case None
    then show ?thesis using lhs rhs by (cases "foldl oqueuePick None es"; simp)
  next
    case (Some x)
    show ?thesis
    proof (cases "foldl oqueuePick None es")
      case None
      then show ?thesis using lhs rhs Some by simp
    next
      case (Some mm)
      obtain z where z: "oqueuePick (Some x) (Some mm) = Some z"
        using oqueuePick_Some_Some by blast
      then show ?thesis
        using lhs rhs \<open>e = Some x\<close> Some oqueuePick_assoc[of acc x mm] by simp
    qed
  qed
qed

lemma oqueue_best_foldl:
  "oqueue_best s l = foldl oqueuePick None (map (oqueue_entry_abs s) l)"
proof (induction l)
  case Nil show ?case by simp
next
  case (Cons t ts)
  show ?case
  proof (cases "oqueue_remaining_budget s t")
    case None
    then show ?thesis by (simp add: oqueue_entry_abs_def Cons.IH)
  next
    case (Some b)
    then have e: "oqueue_entry_abs s t = Some (t, b)"
      by (simp add: oqueue_entry_abs_def)
    show ?thesis
      apply (simp add: Some e)
      apply (subst foldl_oqueuePick_acc)
      apply (simp add: Cons.IH[symmetric])
      apply (cases "oqueue_best s ts")
       apply simp
      apply (auto simp: oqueuePick_def split: prod.splits)
      done
  qed
qed

text \<open>The entry of a thread in a ready queue, read from the Haskell state.\<close>
definition oqueue_entry_conc ::
  "kernel_state \<Rightarrow> machine_word \<Rightarrow> (machine_word \<times> ticks) option"
where
  "oqueue_entry_conc s t \<equiv>
     case tcbs_of' s t of
       None \<Rightarrow> None
     | Some tcb \<Rightarrow>
         if runnable' (tcbState tcb) then Some (t, tcbOQueueBudget tcb) else None"

lemma oqueueEntry_wp:
  "\<lbrace>\<lambda>s. tcb_at' t s \<and> P (oqueue_entry_conc s t) s\<rbrace> oqueueEntry t \<lbrace>P\<rbrace>"
  unfolding oqueueEntry_def
  apply (wpsimp wp: isRunnable_wp threadGet_wp)
  apply (clarsimp simp: oqueue_entry_conc_def obj_at'_def opt_map_def pred_tcb_at'_def
                        projectKO_opt_tcb split: option.splits)
  apply (intro conjI impI allI;
         (drule_tac x=x2 in spec)?;
         clarsimp simp: Let_def split: if_splits)
  done

lemma corres_gets_pure:
  assumes rel: "\<And>s s'. \<lbrakk>(s, s') \<in> state_relation; P s; P' s'\<rbrakk> \<Longrightarrow> a s = e s'"
  assumes hoare: "\<And>X. \<lbrace>\<lambda>s'. s' = X \<and> P' s'\<rbrace> g \<lbrace>\<lambda>r s'. s' = X \<and> r = e X\<rbrace>"
  assumes nf: "no_fail P' g"
  shows "corres (=) P P' (gets a) g"
proof -
  have res: "\<And>s' r' t'. \<lbrakk>P' s'; (r', t') \<in> fst (g s')\<rbrakk> \<Longrightarrow> r' = e s' \<and> t' = s'"
    using use_valid[OF _ hoare] by fastforce
  show ?thesis
    by (fastforce simp: corres_underlying_def simpler_gets_def dest: res no_failD[OF nf] rel)
qed

lemma no_fail_isRunnable:
  "no_fail (tcb_at' t) (isRunnable t)"
  by (simp add: isRunnable_def2 liftM_def, wp, simp)

lemma oqueueEntry_no_fail:
  "no_fail (tcb_at' t) (oqueueEntry t)"
  unfolding oqueueEntry_def
  by (wpsimp wp: no_fail_isRunnable)

lemma oqueueEntry_hoare:
  "\<lbrace>\<lambda>s'. s' = X \<and> tcb_at' t s'\<rbrace> oqueueEntry t
   \<lbrace>\<lambda>r s'. s' = X \<and> r = oqueue_entry_conc X t\<rbrace>"
  by (rule hoare_weaken_pre[OF oqueueEntry_wp[where P="\<lambda>r s'. s' = X \<and> r = oqueue_entry_conc X t"]]; simp)

lemma thread_state_relation_runnable:
  "thread_state_relation ts ts' \<Longrightarrow> runnable ts = runnable' ts'"
  by (cases ts; clarsimp simp: thread_state_relation_def)

lemma oqueue_entry_rel:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation" and ta: "tcb_at t s"
  assumes al: "pspace_aligned s" and di: "pspace_distinct s"
  shows "oqueue_entry_abs s t = oqueue_entry_conc s' t"
proof -
  from ta obtain tcb where g: "get_tcb t s = Some tcb"
    by (auto simp: tcb_at_def)
  hence ko: "ko_at (TCB tcb) t s"
    by (simp add: get_tcb_ko_at)
  from ko_tcb_cross[OF ko al di sr]
  obtain tcb' where ko': "ko_at' tcb' t s'" and rel: "tcb_relation tcb tcb'"
    by blast
  from ko' have g': "tcbs_of' s' t = Some tcb'"
    by (clarsimp simp: obj_at'_def opt_map_def projectKO_opt_tcb)
  from rel have tsr: "thread_state_relation (tcb_state tcb) (tcbState tcb')"
    by (simp add: tcb_relation_def)
  hence tr: "runnable (tcb_state tcb) = runnable' (tcbState tcb')"
    by (rule thread_state_relation_runnable)
  show ?thesis
    using g g' rel tr
    by (clarsimp simp: oqueue_entry_abs_def oqueue_remaining_budget_def oqueue_entry_conc_def
                       tcb_relation_def split: if_splits)
qed

lemma oqueueEntry_corres:
  "corres (=)
     (tcb_at t and pspace_aligned and pspace_distinct)
     (tcb_at' t)
     (gets (\<lambda>s::det_state. oqueue_entry_abs s t)) (oqueueEntry t)"
  apply (rule corres_gets_pure[where e="\<lambda>s'. oqueue_entry_conc s' t"])
    apply (fastforce simp: oqueue_entry_rel)
   apply (rule hoare_weaken_pre[OF oqueueEntry_hoare]; simp)
  apply (rule no_fail_pre[OF oqueueEntry_no_fail]; simp)
  done

lemma corres_gets_pure_r:
  assumes rel: "\<And>s s'. \<lbrakk>(s, s') \<in> state_relation; P s; P' s'\<rbrakk> \<Longrightarrow> r (a s) (e s')"
  assumes hoare: "\<And>X. \<lbrace>\<lambda>s'. s' = X \<and> P' s'\<rbrace> g \<lbrace>\<lambda>rv s'. s' = X \<and> rv = e X\<rbrace>"
  assumes nf: "no_fail P' g"
  shows "corres r P P' (gets a) g"
proof -
  have res: "\<And>s' r' t'. \<lbrakk>P' s'; (r', t') \<in> fst (g s')\<rbrakk> \<Longrightarrow> r' = e s' \<and> t' = s'"
    using use_valid[OF _ hoare] by fastforce
  show ?thesis
    by (fastforce simp: corres_underlying_def simpler_gets_def dest: res no_failD[OF nf] rel)
qed

text \<open>The selection the Haskell policy makes, as a function of the Haskell state.\<close>
definition oqueue_sel_conc :: "kernel_state \<Rightarrow> tcb_queue \<Rightarrow> machine_word option" where
  "oqueue_sel_conc s q \<equiv>
     case foldl oqueuePick None (map (oqueue_entry_conc s) (oqueueQueueList s q)) of
       None \<Rightarrow> None
     | Some (t, _) \<Rightarrow> Some t"

lemma mapM_oqueueEntry_wp:
  "\<lbrace>\<lambda>s. (\<forall>t \<in> set l. tcb_at' t s) \<and> P (map (oqueue_entry_conc s) l) s\<rbrace>
   mapM oqueueEntry l
   \<lbrace>P\<rbrace>"
proof (induction l arbitrary: P)
  case Nil
  show ?case by (simp add: mapM_Nil, wp)
next
  case (Cons x xs)
  show ?case
    apply (simp add: mapM_Cons)
    apply (wp Cons.IH oqueueEntry_wp)
    done
qed

lemma oqueue_case_wp:
  "\<lbrace>\<lambda>s. case x of None \<Rightarrow> True | Some (t, _) \<Rightarrow> P t s\<rbrace>
   (case (x :: ('a \<times> 'b) option) of None \<Rightarrow> haskell_fail [] | Some (thread, _) \<Rightarrow> return thread)
   \<lbrace>P\<rbrace>"
  apply (cases x)
   apply clarsimp
  apply (case_tac a, clarsimp?, wp?)
  done

lemma oqueueSelect_wp:
  "\<lbrace>\<lambda>s. (\<forall>t \<in> set (oqueueQueueList s q). tcb_at' t s) \<and> (\<exists>t. oqueue_sel_conc s q = Some t)
        \<and> P (the (oqueue_sel_conc s q)) s\<rbrace>
   oqueueSelect q
   \<lbrace>P\<rbrace>"
  unfolding oqueueSelect_def
  apply (wp oqueue_case_wp mapM_oqueueEntry_wp get_wp)
  apply (clarsimp simp: oqueue_sel_conc_def split: option.splits prod.splits)
  done

lemma oqueueSelect_no_fail:
  "no_fail (\<lambda>s. (\<forall>t \<in> set (oqueueQueueList s q). tcb_at' t s)
                 \<and> (\<exists>t. oqueue_sel_conc s q = Some t)) (oqueueSelect q)"
  unfolding oqueueSelect_def
  apply (rule no_fail_pre)
   apply (rule no_fail_bind[OF _ get_sp[where P="\<lambda>s. (\<forall>t \<in> set (oqueueQueueList s q). tcb_at' t s)
                                                 \<and> (\<exists>t. oqueue_sel_conc s q = Some t)"] no_fail_get])
   apply (rename_tac ks)
   apply (rule no_fail_pre)
    apply (rule no_fail_bind
             [where R="\<lambda>es (s :: kernel_state).
                         \<exists>t. (case foldl oqueuePick None es of None \<Rightarrow> None
                                | Some (t, _) \<Rightarrow> Some t) = Some t",
              OF _ mapM_oqueueEntry_wp[where P="\<lambda>es (s :: kernel_state).
                         \<exists>t. (case foldl oqueuePick None es of None \<Rightarrow> None
                                | Some (t, _) \<Rightarrow> Some t) = Some t"]
                 no_fail_mapM_wp[where P="\<lambda>x. tcb_at' x"]])
       apply (rename_tac es)
       apply (case_tac "foldl oqueuePick None es"; clarsimp split: prod.splits)
      apply (rule oqueueEntry_no_fail)
     apply (rule oqueueEntry_inv)
    apply (clarsimp simp: oqueue_sel_conc_def split: option.splits prod.splits)
   apply (clarsimp simp: oqueue_sel_conc_def split: option.splits prod.splits)
  done

lemma oqueuePick_Some_ne: "oqueuePick (Some x) e \<noteq> None"
  by (cases e; cases x; auto simp: oqueuePick_def split: option.splits prod.splits if_splits)

lemma foldl_oqueuePick_Some_ne:
  "foldl oqueuePick (Some x) es \<noteq> None"
proof (induction es arbitrary: x)
  case Nil show ?case by simp
next
  case (Cons e es)
  obtain y where "oqueuePick (Some x) e = Some y"
    using oqueuePick_Some_ne[of x e] by (cases "oqueuePick (Some x) e") auto
  then show ?case using Cons.IH[of y] by simp
qed

lemma oqueue_entry_conc_runnable:
  "st_tcb_at' runnable' t s' \<Longrightarrow> \<exists>e. oqueue_entry_conc s' t = Some e"
  apply (clarsimp simp: oqueue_entry_conc_def pred_tcb_at'_def obj_at'_def opt_map_def
                        projectKO_opt_tcb tcb_to_itcb'_def split: option.splits)
  done

lemma oqueue_sel_conc_Some:
  assumes l: "oqueueQueueList s' queue = t # ts" and r: "st_tcb_at' runnable' t s'"
  shows "\<exists>t'. oqueue_sel_conc s' queue = Some t'"
proof -
  from oqueue_entry_conc_runnable[OF r]
  obtain e where e: "oqueue_entry_conc s' t = Some e" by blast
  from foldl_oqueuePick_Some_ne[of e "map (oqueue_entry_conc s') ts"]
  obtain m where m: "foldl oqueuePick (Some e) (map (oqueue_entry_conc s') ts) = Some m"
    by (cases "foldl oqueuePick (Some e) (map (oqueue_entry_conc s') ts)") auto
  show ?thesis
    using e m by (cases m; simp add: oqueue_sel_conc_def l)
qed

lemma oqueue_conc_pre:
  assumes lq: "list_queue_relation Q queue (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  assumes nz: "Q \<noteq> []" and run: "\<forall>t \<in> set Q. st_tcb_at' runnable' t s'"
  shows "(\<forall>t \<in> set (oqueueQueueList s' queue). tcb_at' t s')
         \<and> (\<exists>t. oqueue_sel_conc s' queue = Some t)"
proof -
  have l: "oqueueQueueList s' queue = Q" by (rule oqueueQueueList_eq[OF lq])
  obtain t ts where Q: "Q = t # ts" using nz by (cases Q) auto
  have tc: "\<forall>t \<in> set Q. tcb_at' t s'"
    using run by (fastforce simp: pred_tcb_at'_def obj_at'_def)
  have "\<exists>t'. oqueue_sel_conc s' queue = Some t'"
    using oqueue_sel_conc_Some[of s' queue t ts] l Q run by fastforce
  then show ?thesis using l tc by simp
qed

lemma foldl_oqueuePick_in:
  "foldl oqueuePick acc es = Some m \<Longrightarrow> acc = Some m \<or> Some m \<in> set es"
proof (induction es arbitrary: acc)
  case Nil then show ?case by simp
next
  case (Cons e es)
  from Cons.prems have "foldl oqueuePick (oqueuePick acc e) es = Some m" by simp
  from Cons.IH[OF this] show ?case
    by (cases acc; cases e; fastforce simp: oqueuePick_def split: option.splits prod.splits if_splits)
qed

lemma oqueue_entry_conc_fst:
  "oqueue_entry_conc s t = Some (a, b) \<Longrightarrow> a = t"
  by (clarsimp simp: oqueue_entry_conc_def split: option.splits if_splits)

lemma oqueue_sel_conc_in_list:
  "oqueue_sel_conc s q = Some t \<Longrightarrow> t \<in> set (oqueueQueueList s q)"
  apply (clarsimp simp: oqueue_sel_conc_def split: option.splits prod.splits)
  apply (drule foldl_oqueuePick_in)
  apply (clarsimp simp: image_def)
  apply (fastforce dest: oqueue_entry_conc_fst[OF sym])
  done

lemma oqueueSelect_mem_wp:
  "\<lbrace>\<lambda>s. (\<forall>t \<in> set (oqueueQueueList s q). tcb_at' t s) \<and> (\<exists>t. oqueue_sel_conc s q = Some t)
        \<and> (\<forall>t \<in> set (oqueueQueueList s q). P t s)\<rbrace>
   oqueueSelect q
   \<lbrace>P\<rbrace>"
  by (rule hoare_weaken_pre[OF oqueueSelect_wp]; fastforce dest: oqueue_sel_conc_in_list)

lemma oqueue_select_rel:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation"
  assumes al: "pspace_aligned s" and di: "pspace_distinct s"
  assumes lq: "list_queue_relation Q queue (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  assumes tc: "\<forall>t \<in> set Q. tcb_at t s"
  shows "oqueue_select s Q = oqueue_sel_conc s' queue"
proof -
  have l: "oqueueQueueList s' queue = Q" by (rule oqueueQueueList_eq[OF lq])
  have eq: "map (oqueue_entry_abs s) Q = map (oqueue_entry_conc s') Q"
  proof (rule map_cong[OF refl])
    fix x assume "x \<in> set Q"
    hence "tcb_at x s" using tc by blast
    thus "oqueue_entry_abs s x = oqueue_entry_conc s' x"
      by (rule oqueue_entry_rel[OF sr _ al di])
  qed
  show ?thesis
    by (simp add: oqueue_select_def oqueue_sel_conc_def oqueue_best_foldl l eq)
qed

lemma oqueue_select_rel_Some:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation"
  assumes al: "pspace_aligned s" and di: "pspace_distinct s"
  assumes lq: "list_queue_relation Q queue (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  assumes nz: "Q \<noteq> []"
  assumes run': "\<forall>t \<in> set Q. st_tcb_at' runnable' t s'"
  assumes run: "\<forall>t \<in> set Q. st_tcb_at runnable t s"
  shows "oqueue_select s Q = Some (the (oqueue_sel_conc s' queue))"
proof -
  have tc: "\<forall>t \<in> set Q. tcb_at t s" using run by (fastforce simp: st_tcb_at_tcb_at)
  have r: "oqueue_select s Q = oqueue_sel_conc s' queue"
    by (rule oqueue_select_rel[OF sr al di lq tc])
  obtain t where "oqueue_sel_conc s' queue = Some t"
    using oqueue_conc_pre[OF lq nz run'] by blast
  thus ?thesis using r by simp
qed

lemma oqueueSelect_corres:
  assumes nz: "Q \<noteq> []"
  shows "corres (\<lambda>c t. c = Some t)
           (pspace_aligned and pspace_distinct
            and (\<lambda>s. \<forall>t \<in> set Q. st_tcb_at runnable t s))
           ((\<lambda>s'. list_queue_relation Q queue (tcbSchedNexts_of s') (tcbSchedPrevs_of s'))
            and (\<lambda>s'. \<forall>t \<in> set Q. st_tcb_at' runnable' t s'))
           (gets (\<lambda>s::det_state. oqueue_select s Q)) (oqueueSelect queue)"
  apply (rule corres_gets_pure_r[where e="\<lambda>s'. the (oqueue_sel_conc s' queue)"])
    apply (clarsimp, rule oqueue_select_rel_Some[OF _ _ _ _ nz]; assumption)
   apply (rule hoare_weaken_pre[OF oqueueSelect_wp])
   apply (fastforce dest: oqueue_conc_pre[OF _ nz])
  apply (rule no_fail_pre[OF oqueueSelect_no_fail])
  apply (fastforce dest: oqueue_conc_pre[OF _ nz])
  done

context Schedule_R begin

lemma switchToIdleThread_curr_is_idle:
  "\<lbrace>\<top>\<rbrace> switchToIdleThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s\<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (wps switchToIdleThread_it)
   apply (simp add: Thread_H.switchToIdleThread_def)
   apply (wp setCurThread_const)
  apply (simp)
 done

lemma chooseThread_it[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> chooseThread \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  supply if_split[split del]
  by (wpsimp simp: chooseThread_def curDomain_def bitmap_fun_defs)

end (* Schedule_R *)

lemma corres_split_sched_act:
  "\<lbrakk>sched_act_relation act act';
    corres r P P' f1 g1;
    \<And>t. corres r (Q t) (Q' t) (f2 t) (g2 t);
    corres r R R' f3 g3\<rbrakk>
    \<Longrightarrow> corres r (case act of resume_cur_thread \<Rightarrow> P
                           | switch_thread t \<Rightarrow> Q t
                           | choose_new_thread \<Rightarrow> R)
               (case act' of ResumeCurrentThread \<Rightarrow> P'
                           | SwitchToThread t \<Rightarrow> Q' t
                           | ChooseThread \<Rightarrow> R')
       (case act of resume_cur_thread \<Rightarrow> f1
                  | switch_thread t \<Rightarrow> f2 t
                  | choose_new_thread \<Rightarrow> f3)
       (case act' of ResumeCurrentThread \<Rightarrow> g1
                   | ChooseNewThread \<Rightarrow> g3
                   | SwitchToThread t \<Rightarrow> g2 t)"
  apply (cases act)
    apply (rule corres_guard_imp, force+)+
    done

lemma corres_assert_ret:
  "corres dc (\<lambda>s. P) \<top> (assert P) (return ())"
  apply (rule corres_no_failI)
   apply simp
  apply (simp add: assert_def return_def fail_def)
  done

lemma corres_assert_assume_r:
  "corres dc P Q f (g ())
  \<Longrightarrow> corres dc P (Q and (\<lambda>s. Q')) f (assert Q' >>= g)"
  by (force simp: corres_underlying_def assert_def return_def bind_def fail_def)

lemma gts_exs_valid[wp]:
  "tcb_at t s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_thread_state t \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_thread_state_def  assert_opt_def fail_def
             thread_get_def gets_the_def exs_valid_def gets_def
             get_def bind_def return_def split: option.splits)
  apply (erule get_tcb_at)
  done

lemma (in Schedule_R) guarded_switch_to_corres:
  "corres dc (valid_arch_state and valid_objs and valid_asid_map
                and valid_vspace_objs and pspace_aligned and pspace_distinct
                and valid_arch_caps and valid_global_objs and pspace_in_kernel_window
                and st_tcb_at runnable t and (\<lambda>s. sym_refs (state_hyp_refs_of s))
                and valid_queues and valid_idle and valid_cur_fpu)
             (no_0_obj' and sym_heap_sched_pointers and valid_objs')
             (guarded_switch_to t) (switchToThread t)"
  apply (simp add: guarded_switch_to_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_l'[OF _ gts_exs_valid])
      apply (rule corres_assert_assume_l)
      apply (rule switchToThread_corres)
     apply (force simp: st_tcb_at_tcb_at)
    apply (wp gts_st_tcb_at)
   apply (force simp: st_tcb_at_tcb_at)+
  done

abbreviation "enumPrio \<equiv> [0.e.maxPriority]"

lemma enumPrio_word_div:
  fixes v :: "8 word"
  assumes vlt: "unat v \<le> unat maxPriority"
  shows "\<exists>xs ys. enumPrio = xs @ [v] @ ys \<and> (\<forall>x\<in>set xs. x < v) \<and> (\<forall>y\<in>set ys. v < y)"
  apply (subst upto_enum_word)
  apply (subst upt_add_eq_append'[where j="unat v"])
    apply simp
   apply (rule le_SucI)
   apply (rule vlt)
  apply (simp only: upt_conv_Cons vlt[simplified less_Suc_eq_le[symmetric]])
  apply (intro exI conjI)
    apply fastforce
   apply clarsimp
   apply (drule of_nat_mono_maybe[rotated, where 'a="8"])
    apply (fastforce simp: vlt)
   apply simp
  apply (clarsimp simp: Suc_le_eq)
  apply (erule disjE)
   apply (drule of_nat_mono_maybe[rotated, where 'a="8"])
    apply (simp add: maxPriority_def numPriorities_def)
   apply (clarsimp simp: unat_of_nat_eq)
  apply (erule conjE)
  apply (drule_tac y="unat v" and x="x" in of_nat_mono_maybe[rotated, where 'a="8"])
   apply (simp add: maxPriority_def numPriorities_def)+
  done

lemma curDomain_corres: "corres (=) \<top> \<top> (gets cur_domain) (curDomain)"
  by (simp add: curDomain_def state_relation_def)

lemma curDomain_corres':
  "corres (=) \<top> (\<lambda>s. ksCurDomain s \<le> maxDomain)
    (gets cur_domain) (if Suc 0 < numDomains then curDomain else return 0)"
  apply (case_tac "1 < numDomains"; simp)
   apply (rule corres_guard_imp[OF curDomain_corres]; solves simp)
  (* if we have only one domain, then we are in it *)
  apply (clarsimp simp: return_def simpler_gets_def bind_def maxDomain_def
                        state_relation_def corres_underlying_def)
  done

locale Schedule_R_2 = Schedule_R +
  assumes bitmapL1_highest_lookup:
    "\<And>s d p.
     \<lbrakk> valid_bitmapQ s; bitmapQ_no_L1_orphans s; bitmapQ d p s \<rbrakk>
     \<Longrightarrow> p \<le> lookupBitmapPriority d s"
  assumes guarded_switch_to_chooseThread_fragment_corres:
    "\<And>P P' t.
     corres dc
      (P and st_tcb_at runnable t and invs and valid_sched)
      (P' and invs_no_cicd')
      (guarded_switch_to t)
      (do runnable \<leftarrow> isRunnable t;
          y \<leftarrow> assert runnable;
          ThreadDecls_H.switchToThread t
       od)"
  assumes tcb_sched_action_valid_vs_lookup[wp]:
    "tcb_sched_action action t \<lbrace>\<lambda>s::det_state. valid_vs_lookup s\<rbrace>"
begin

lemma lookupBitmapPriority_Max_eqI:
  "\<lbrakk> valid_bitmapQ s ; bitmapQ_no_L1_orphans s ; ksReadyQueuesL1Bitmap s d \<noteq> 0 \<rbrakk>
   \<Longrightarrow> lookupBitmapPriority d s = (Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s (d, prio))})"
  apply (rule Max_eqI[simplified eq_commute]; simp)
   apply (fastforce simp: bitmapL1_highest_lookup valid_bitmapQ_bitmapQ_simp)
  apply (metis valid_bitmapQ_bitmapQ_simp bitmapQ_from_bitmap_lookup)
  done

end (* Schedule_R_2 *)

lemma (in Schedule_R) corres_gets_queues_getReadyQueuesL1Bitmap:
  "corres (\<lambda>qs l1. (l1 = 0) = (\<forall>p. qs p = [])) \<top> valid_bitmaps
    (gets (\<lambda>s. ready_queues s d)) (getReadyQueuesL1Bitmap d)"
  unfolding state_relation_def valid_bitmaps_def getReadyQueuesL1Bitmap_def
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  apply (drule_tac x=d in spec)
  apply (fastforce simp: bitmapL1_zero_ksReadyQueues list_queue_relation_def tcbQueueEmpty_def)
  done

lemma Max_prio_helper:
  "ready_queues_relation s s'
   \<Longrightarrow> Max {prio. ready_queues s d prio \<noteq> []}
       = Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s' (d, prio))}"
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def tcbQueueEmpty_def)
  apply (rule Max_eq_if)
     apply fastforce
    apply fastforce
   apply (fastforce dest: heap_path_head)
  apply clarsimp
  apply (drule_tac x=d in spec)
  apply (drule_tac x=b in spec)
  apply force
  done

lemma (in Schedule_R_2) bitmap_lookup_queue_is_max_non_empty:
  "\<lbrakk> valid_bitmaps s'; (s, s') \<in> state_relation; invs s;
     ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0 \<rbrakk>
   \<Longrightarrow> the (tcbQueueHead (ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')))
       = hd (max_non_empty_queue (ready_queues s (cur_domain s)))"
  apply (clarsimp simp: max_non_empty_queue_def valid_bitmaps_def lookupBitmapPriority_Max_eqI)
  apply (frule curdomain_relation)
  apply (drule state_relation_ready_queues_relation)
  apply (simp add: Max_prio_helper)
  apply (clarsimp simp: ready_queues_relation_def ready_queue_relation_def Let_def
                        list_queue_relation_def)
  apply (frule (2) bitmapL1_zero_ksReadyQueues[THEN arg_cong_Not, THEN iffD1])
  apply clarsimp
  apply (cut_tac P="\<lambda>x. \<not> tcbQueueEmpty (ksReadyQueues s' (ksCurDomain s', x))"
              in setcomp_Max_has_prop)
   apply fastforce
  apply (clarsimp simp: ready_queues_relation_def Let_def list_queue_relation_def tcbQueueEmpty_def)
  apply (drule_tac x="ksCurDomain s'" in spec)
  apply (drule_tac x="Max {prio. \<not> tcbQueueEmpty (ksReadyQueues s' (ksCurDomain s', prio))}"
                in spec)
  apply clarsimp
  apply (frule heap_path_head')
  apply (clarsimp simp: headEndPtrsEmpty_def)
  done

lemma ksReadyQueuesL1Bitmap_return_wp:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s d) s \<rbrace> getReadyQueuesL1Bitmap d \<lbrace>\<lambda>rv s. P rv s\<rbrace>"
  unfolding getReadyQueuesL1Bitmap_def
  by wp

lemma curDomain_or_return_0:
  "\<lbrakk> \<lbrace>P\<rbrace> curDomain \<lbrace>\<lambda>rv s. Q rv s \<rbrace>; \<And>s. P s \<Longrightarrow> ksCurDomain s \<le> maxDomain \<rbrakk>
   \<Longrightarrow> \<lbrace>P\<rbrace> if 1 < numDomains then curDomain else return 0 \<lbrace>\<lambda>rv s. Q rv s \<rbrace>"
  apply (case_tac "1 < numDomains"; simp)
  apply (simp add: valid_def curDomain_def simpler_gets_def return_def maxDomain_def)
  done

lemma invs_no_cicd_ksCurDomain_maxDomain':
  "invs_no_cicd' s \<Longrightarrow> ksCurDomain s \<le> maxDomain"
  unfolding invs_no_cicd'_def by simp

crunch curDomain
  for valid_bitmaps[wp]: valid_bitmaps

lemma valid_queues_max_runnable:
  "\<lbrakk>valid_queues s; t \<in> set (max_non_empty_queue (ready_queues s d))\<rbrakk>
   \<Longrightarrow> st_tcb_at runnable t s"
  for s :: "'z::state_ext state"
  by (fastforce simp: valid_queues_def max_non_empty_queue_def)

lemma max_non_empty_queue_ne:
  assumes h: "\<not> (\<forall>p. queues p = [])"
  shows "max_non_empty_queue queues \<noteq> []"
proof -
  from h have e: "\<exists>p. queues p \<noteq> []" by auto
  then obtain p0 where "queues p0 \<noteq> []" by blast
  from setcomp_Max_has_prop[where P="\<lambda>p. queues p \<noteq> []", OF this]
  show ?thesis by (simp add: max_non_empty_queue_def)
qed

lemma (in Schedule_R_2) bitmap_lookup_queue_relation:
  "\<lbrakk> valid_bitmaps s'; (s, s') \<in> state_relation; invs s;
     ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0 \<rbrakk>
   \<Longrightarrow> list_queue_relation (max_non_empty_queue (ready_queues s (cur_domain s)))
         (ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s'))
         (tcbSchedNexts_of s') (tcbSchedPrevs_of s')"
  apply (clarsimp simp: max_non_empty_queue_def valid_bitmaps_def lookupBitmapPriority_Max_eqI)
  apply (frule curdomain_relation)
  apply (drule state_relation_ready_queues_relation)
  apply (simp add: Max_prio_helper)
  apply (fastforce simp: ready_queues_relation_def ready_queue_relation_def Let_def)
  done

lemma (in Schedule_R_2) oqueueSelect_facts:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation" and iv: "invs s" and vq: "valid_queues s"
  assumes ne: "\<not> (\<forall>p. ready_queues s (cur_domain s) p = [])"
  assumes vb: "valid_bitmaps s'" and l1: "ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0"
  shows "list_queue_relation (max_non_empty_queue (ready_queues s (cur_domain s)))
           (ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s'))
           (tcbSchedNexts_of s') (tcbSchedPrevs_of s')
         \<and> max_non_empty_queue (ready_queues s (cur_domain s)) \<noteq> []
         \<and> (\<forall>t \<in> set (max_non_empty_queue (ready_queues s (cur_domain s))). st_tcb_at runnable t s)
         \<and> (\<forall>t \<in> set (max_non_empty_queue (ready_queues s (cur_domain s))).
              st_tcb_at' runnable' t s')"
proof -
  have run: "\<forall>t \<in> set (max_non_empty_queue (ready_queues s (cur_domain s))).
               st_tcb_at runnable t s"
    using vq by (blast intro: valid_queues_max_runnable)
  show ?thesis
    using bitmap_lookup_queue_relation[OF vb sr iv l1] max_non_empty_queue_ne[OF ne] run sr iv
    by (fastforce intro: st_tcb_at_runnable_cross)
qed

lemma corres_gets_pure_rel:
  assumes rel: "\<And>s s'. \<lbrakk>(s, s') \<in> state_relation; P s; P' s'\<rbrakk> \<Longrightarrow> r (a s) (e s')"
  assumes hoare: "\<And>s s'. \<lbrakk>(s, s') \<in> state_relation; P s; P' s'\<rbrakk>
                   \<Longrightarrow> \<lbrace>\<lambda>s''. s'' = s'\<rbrace> g \<lbrace>\<lambda>rv s''. s'' = s' \<and> rv = e s'\<rbrace>"
  assumes nf: "\<And>s s'. \<lbrakk>(s, s') \<in> state_relation; P s; P' s'\<rbrakk> \<Longrightarrow> \<not> snd (g s')"
  shows "corres r P P' (gets a) g"
proof -
  have main: "\<And>s s' r' t'. \<lbrakk>(s, s') \<in> state_relation; P s; P' s'; (r', t') \<in> fst (g s')\<rbrakk>
                            \<Longrightarrow> r' = e s' \<and> t' = s'"
  proof -
    fix s s' r' t'
    assume a: "(s, s') \<in> state_relation" "P s" "P' s'" and m: "(r', t') \<in> fst (g s')"
    from use_valid[OF m hoare[OF a]] show "r' = e s' \<and> t' = s'" by simp
  qed
  show ?thesis
    apply (clarsimp simp: corres_underlying_def simpler_gets_def)
    apply (rename_tac s s')
    apply (intro conjI)
     apply clarsimp
     apply (rename_tac r' t')
     apply (frule (3) main)
     apply (fastforce dest: rel)
    apply (rule nf; assumption)
    done
qed

lemma (in Schedule_R_2) oqueueSelect_rel_branch:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation" and iv: "invs s" and vq: "valid_queues s"
  assumes ne: "\<exists>p. ready_queues s (cur_domain s) p \<noteq> []"
  assumes vb: "valid_bitmaps s'" and l1: "ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0"
  assumes Qd: "Q = max_non_empty_queue (ready_queues s (cur_domain s))"
  assumes qd: "queue = ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')"
  shows "oqueue_select s Q = Some (the (oqueue_sel_conc s' queue))"
proof -
  from ne have ne': "\<not> (\<forall>p. ready_queues s (cur_domain s) p = [])" by auto
  note f = oqueueSelect_facts[OF sr iv vq ne' vb l1]
  show ?thesis
    unfolding Qd qd
    by (rule oqueue_select_rel_Some[OF sr invs_psp_aligned[OF iv] invs_distinct[OF iv]
              f[THEN conjunct1] f[THEN conjunct2, THEN conjunct1]
              f[THEN conjunct2, THEN conjunct2, THEN conjunct2]
              f[THEN conjunct2, THEN conjunct2, THEN conjunct1]])
qed

lemma (in Schedule_R_2) oqueueSelect_conc_pre_branch:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation" and iv: "invs s" and vq: "valid_queues s"
  assumes ne: "\<exists>p. ready_queues s (cur_domain s) p \<noteq> []"
  assumes vb: "valid_bitmaps s'" and l1: "ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0"
  assumes qd: "queue = ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')"
  shows "(\<forall>t \<in> set (oqueueQueueList s' queue). tcb_at' t s')
         \<and> (\<exists>t. oqueue_sel_conc s' queue = Some t)"
proof -
  from ne have ne': "\<not> (\<forall>p. ready_queues s (cur_domain s) p = [])" by auto
  note f = oqueueSelect_facts[OF sr iv vq ne' vb l1]
  show ?thesis
    unfolding qd
    by (rule oqueue_conc_pre[OF f[THEN conjunct1] f[THEN conjunct2, THEN conjunct1]
                                f[THEN conjunct2, THEN conjunct2, THEN conjunct2]])
qed

lemma (in Schedule_R_2) oqueueSelect_branches:
  fixes s :: det_state
  assumes sr: "(s, s') \<in> state_relation"
  assumes pa: "(invs and valid_queues
      and (\<lambda>s. Q = max_non_empty_queue (ready_queues s (cur_domain s)))
      and (\<lambda>s. \<exists>p. ready_queues s (cur_domain s) p \<noteq> [])
      ) s"
  assumes pc: "(\<lambda>s'. queue = ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')
            \<and> valid_bitmaps s' \<and> ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0) s'"
  shows "oqueue_select s Q = Some (the (oqueue_sel_conc s' queue))
         \<and> (\<forall>t \<in> set (oqueueQueueList s' queue). tcb_at' t s')
         \<and> (\<exists>t. oqueue_sel_conc s' queue = Some t)"
proof -
  from pa have iv: "invs s" and vq: "valid_queues s"
    and Qd: "Q = max_non_empty_queue (ready_queues s (cur_domain s))"
    and ne: "\<exists>p. ready_queues s (cur_domain s) p \<noteq> []"
    by (simp_all add: pred_conj_def)
  from pc have qd: "queue = ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')"
    and vb: "valid_bitmaps s'" and l1: "ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0"
    by simp_all
  show ?thesis
    by (intro conjI oqueueSelect_rel_branch[OF sr iv vq ne vb l1 Qd qd]
              oqueueSelect_conc_pre_branch[OF sr iv vq ne vb l1 qd, THEN conjunct1]
              oqueueSelect_conc_pre_branch[OF sr iv vq ne vb l1 qd, THEN conjunct2])
qed

lemma (in Schedule_R_2) oqueueSelect_corres':
  "corres (\<lambda>c t. c = Some t)
     (invs and valid_queues
      and (\<lambda>s. Q = max_non_empty_queue (ready_queues s (cur_domain s)))
      and (\<lambda>s. \<exists>p. ready_queues s (cur_domain s) p \<noteq> [])
      )
     ((\<lambda>s'. queue = ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')
            \<and> valid_bitmaps s' \<and> ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0))
     (gets (\<lambda>s::det_state. oqueue_select s Q)) (oqueueSelect queue)"
  apply (rule corres_gets_pure_rel[where e="\<lambda>s'. the (oqueue_sel_conc s' queue)"])
    apply (drule (2) oqueueSelect_branches)
    apply simp
   apply (frule (2) oqueueSelect_branches)
   apply (rule hoare_weaken_pre[OF oqueueSelect_wp])
   apply fastforce
  apply (frule (2) oqueueSelect_branches)
  apply (cut_tac oqueueSelect_no_fail[where q=queue])
  apply (fastforce simp: no_fail_def)
  done

lemma valid_queues_hd_runnable:
  assumes vq: "valid_queues s" and ne: "ready_queues s d p \<noteq> []"
  shows "st_tcb_at runnable (hd (max_non_empty_queue (ready_queues s d))) s"
proof -
  have "\<not> (\<forall>p. ready_queues s d p = [])" using ne by auto
  hence "max_non_empty_queue (ready_queues s d) \<noteq> []" by (rule max_non_empty_queue_ne)
  thus ?thesis using vq by (fastforce intro: valid_queues_max_runnable hd_in_set)
qed

lemma (in Schedule_R_2) chooseThread_policy_corres:
  "corres dc
    (invs and valid_sched
     and (\<lambda>s. queues = ready_queues s (cur_domain s))
     and (\<lambda>s. \<exists>p. ready_queues s (cur_domain s) p \<noteq> []))
    (invs_no_cicd'
     and (\<lambda>s'. ksReadyQueuesL1Bitmap s' (ksCurDomain s') \<noteq> 0
              \<and> queue = ksReadyQueues s' (ksCurDomain s', lookupBitmapPriority (ksCurDomain s') s')))
    (do s \<leftarrow> get;
        y \<leftarrow> assert (\<exists>y. oqueue_select s (max_non_empty_queue queues) = Some y);
        guarded_switch_to (the (oqueue_select s (max_non_empty_queue queues)))
     od)
    (do thread \<leftarrow> oqueueSelect queue;
        runnable \<leftarrow> isRunnable thread;
        y \<leftarrow> assert runnable;
        switchToThread thread
     od)"
proof -
  have eq: "(do s \<leftarrow> get;
              y \<leftarrow> assert (\<exists>y. oqueue_select s (max_non_empty_queue queues) = Some y);
              guarded_switch_to (the (oqueue_select s (max_non_empty_queue queues)))
           od) =
           (do c \<leftarrow> gets (\<lambda>s. oqueue_select s (max_non_empty_queue queues));
               y \<leftarrow> assert (\<exists>y. c = Some y);
               guarded_switch_to (the c)
            od)"
    by (simp add: gets_def bind_assoc)
  show ?thesis
    apply (subst eq)
    apply (rule corres_guard_imp)
      apply (rule corres_split
               [where R="\<lambda>c s. c = oqueue_select s (max_non_empty_queue queues)
                                \<and> invs s \<and> valid_sched s \<and> queues = ready_queues s (cur_domain s)"
                  and R'="\<lambda>_ s. invs_no_cicd' s",
                OF oqueueSelect_corres'[where Q="max_non_empty_queue queues" and queue=queue]])
         apply clarsimp
         apply (rename_tac t)
         apply (rule corres_guard_imp)
           apply (rule_tac P=\<top> and P'=\<top> in guarded_switch_to_chooseThread_fragment_corres)
          apply (fastforce dest: oqueue_select_in_queue[OF sym] intro: valid_queues_max_runnable
                           simp: pred_conj_def valid_sched_def)
         apply (simp add: pred_conj_def)
        apply wp
       apply wp
      apply (clarsimp simp: pred_conj_def valid_sched_def)
     apply (clarsimp simp: pred_conj_def all_invs_but_ct_idle_or_in_cur_domain'_def)
     done
qed

lemma (in Schedule_R_2) chooseThread_corres:
  "corres dc
     (invs and valid_sched)
     invs_no_cicd'
     choose_thread chooseThread"
  (is "corres _ ?PREI ?PREH _ _")
proof -

  (* if we only have one domain, we are in it *)
  have one_domain_case:
    "\<And>s. \<lbrakk> invs_no_cicd' s; numDomains \<le> 1 \<rbrakk> \<Longrightarrow> ksCurDomain s = 0"
    by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def maxDomain_def)

  show ?thesis
    supply if_split[split del]
    apply (clarsimp simp: choose_thread_def chooseThread_def)
    apply add_ready_qs_runnable
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply (fastforce intro: ksReadyQueues_asrt_cross)
    apply (rule corres_stateAssert_add_assertion[rotated])
     apply fastforce
    apply (simp only: return_bind Let_def)
    apply (subst if_swap[where P="_ \<noteq> 0"]) (* put switchToIdleThread on first branch*)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF curDomain_corres'])
        apply clarsimp
        apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
          apply (erule corres_if2[OF sym])
           apply (rule switchToIdleThread_corres)
          apply (rule corres_symb_exec_r)
             apply (rule corres_symb_exec_r)
                apply (rule_tac P="\<lambda>s. ?PREI s \<and> queues = ready_queues s (cur_domain s)
                                       \<and> (\<exists>p. ready_queues s (cur_domain s) p \<noteq> [])
                                       \<and> st_tcb_at runnable (hd (max_non_empty_queue queues)) s"
                            and P'="\<lambda>s. ?PREH s \<and> l1 = ksReadyQueuesL1Bitmap s (ksCurDomain s)
                                        \<and> l1 \<noteq> 0
                                        \<and> queue = ksReadyQueues s (ksCurDomain s,
                                                                   lookupBitmapPriority (ksCurDomain s) s)"
                            and F="the (tcbQueueHead queue) = hd (max_non_empty_queue queues)"
                             in corres_req)
                 apply (fastforce simp: bitmap_lookup_queue_is_max_non_empty
                                        all_invs_but_ct_idle_or_in_cur_domain'_def)
                apply clarsimp
                apply (rule corres_guard_imp)
                  apply (rule_tac queues=queues and queue=queue in chooseThread_policy_corres)
                 apply (wpsimp simp: getQueue_def getReadyQueuesL2Bitmap_def)+
        apply (wp hoare_vcg_conj_lift hoare_vcg_imp_lift ksReadyQueuesL1Bitmap_return_wp)
       apply (wpsimp wp: curDomain_or_return_0 simp: curDomain_def)+
     apply (clarsimp simp: valid_sched_def max_non_empty_queue_def valid_queues_def split: if_splits)
     apply (erule_tac x="cur_domain s" in allE)
     apply (erule_tac x="Max {prio. ready_queues s (cur_domain s) prio \<noteq> []}" in allE)
     apply (case_tac "ready_queues s (cur_domain s)
                                     (Max {prio. ready_queues s (cur_domain s) prio
                      \<noteq> []})")
      apply (clarsimp)
      apply (subgoal_tac "ready_queues s (cur_domain s)
                                         (Max {prio. ready_queues s (cur_domain s) prio \<noteq> []})
                          \<noteq> []")
       apply fastforce
      apply (fastforce elim!: setcomp_Max_has_prop)
     apply fastforce
    apply clarsimp
    apply (frule invs_no_cicd_ksCurDomain_maxDomain')
    apply (prop_tac "valid_bitmaps s")
     apply (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def)
    apply (fastforce dest: one_domain_case split: if_splits)
    done
qed

lemma thread_get_comm: "do x \<leftarrow> thread_get f p; y \<leftarrow> gets g; k x y od =
           do y \<leftarrow> gets g; x \<leftarrow> thread_get f p; k x y od"
  apply (rule ext)
  apply (clarsimp simp add: gets_the_def assert_opt_def
                   bind_def gets_def get_def return_def
                   thread_get_def
                   fail_def split: option.splits)
  done

lemma schact_bind_inside: "do x \<leftarrow> f; (case act of resume_cur_thread \<Rightarrow> f1 x
                     | switch_thread t \<Rightarrow> f2 t x
                     | choose_new_thread \<Rightarrow> f3 x) od
          = (case act of resume_cur_thread \<Rightarrow> (do x \<leftarrow> f; f1 x od)
                     | switch_thread t \<Rightarrow> (do x \<leftarrow> f; f2 t x od)
                     | choose_new_thread \<Rightarrow> (do x \<leftarrow> f; f3 x od))"
  apply (case_tac act,simp_all)
  done

lemma getDomainTime_corres:
  "corres (=) \<top> \<top> (gets domain_time) getDomainTime"
  by (simp add: getDomainTime_def state_relation_def)

lemma reset_work_units_equiv:
  "do_extended_op (modify (work_units_completed_update (\<lambda>_. 0)))
   = (modify (work_units_completed_update (\<lambda>_. 0)))"
  by (clarsimp simp: reset_work_units_def[symmetric])

lemma nextDomain_corres:
  "corres dc valid_domain_list \<top> next_domain nextDomain"
  apply (clarsimp simp: next_domain_def nextDomain_def reset_work_units_equiv modify_modify)
  apply (rule corres_modify)
  apply (simp add: state_relation_def Let_def dschLength_def dschDomain_def cdt_relation_def)
  apply clarsimp
  apply (drule sym[where t="ksDomSchedule s" for s])
  apply (clarsimp simp: valid_domain_list_def split_def domain_end_marker_def domainEndMarker_def
                        all_set_conv_all_nth)
  by (force simp: ucast_eq_0 is_up split_pairs2)

lemma next_domain_valid_sched[wp]:
  "\<lbrace> valid_sched and (\<lambda>s. scheduler_action s  = choose_new_thread)\<rbrace> next_domain \<lbrace> \<lambda>_. valid_sched \<rbrace>"
  apply (simp add: next_domain_def Let_def)
  apply (wpsimp wp: dxo_wp_weak)
  apply (clarsimp simp: valid_sched_def)
  done

lemma nextDomain_invs_no_cicd':
  "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread)\<rbrace> nextDomain \<lbrace> \<lambda>_. invs_no_cicd' \<rbrace>"
  apply (simp add: nextDomain_def Let_def dschLength_def dschDomain_def)
  apply wp
  apply (clarsimp simp: invs'_def valid_state'_def valid_machine_state'_def
                        ct_not_inQ_def cur_tcb'_def ct_idle_or_in_cur_domain'_def
                        all_invs_but_ct_idle_or_in_cur_domain'_def
                        valid_dom_schedule'_def split_def domainEndMarker_def)
  apply (metis diff_Suc_Suc linorder_neqE_nat minus_nat.diff_0 not_less_eq)
  done

lemma scheduleSwitchThreadFastfail_corres:
  "\<lbrakk> ct \<noteq> it \<longrightarrow> (tp = tp' \<and> cp = cp') ; ct = ct' ; it = it' \<rbrakk> \<Longrightarrow>
   corres ((=)) (is_tcb_at ct) (tcb_at' ct)
     (schedule_switch_thread_fastfail ct it cp tp)
     (scheduleSwitchThreadFastfail ct' it' cp' tp')"
  by (clarsimp simp: schedule_switch_thread_fastfail_def scheduleSwitchThreadFastfail_def)

lemma gets_is_highest_prio_expand:
  "gets (is_highest_prio d p) \<equiv> do
    q \<leftarrow> gets (\<lambda>s. ready_queues s d);
    return ((\<forall>p. q p = []) \<or> Max {prio. q prio \<noteq> []} \<le> p)
   od"
  by (clarsimp simp: is_highest_prio_def gets_def)

lemma (in Schedule_R_2) isHighestPrio_corres:
  assumes "d' = d"
  assumes "p' = p"
  shows
    "corres ((=)) \<top> valid_bitmaps
      (gets (is_highest_prio d p))
      (isHighestPrio d' p')"
  using assms
  apply (clarsimp simp: gets_is_highest_prio_expand isHighestPrio_def)
  apply (subst getHighestPrio_def')
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF corres_gets_queues_getReadyQueuesL1Bitmap])
      apply (rule corres_if_r'[where P'="\<lambda>_. True",rotated])
       apply (rule_tac corres_symb_exec_r)
          apply (rule_tac P="\<lambda>s. q = ready_queues s d"
                      and P'="\<lambda>s. valid_bitmaps s \<and> l1 = ksReadyQueuesL1Bitmap s d \<and>
                                  l1 \<noteq> 0 \<and> hprio = lookupBitmapPriority d s"
                      and F="hprio = Max {prio. q prio \<noteq> []}" in corres_req)
           apply (elim conjE)
           apply (clarsimp simp: valid_bitmaps_def)
           apply (subst lookupBitmapPriority_Max_eqI; blast?)
           apply (fastforce dest: state_relation_ready_queues_relation Max_prio_helper[where d=d]
                            simp: tcbQueueEmpty_def)
          apply fastforce
         apply (wpsimp simp: if_apply_def2 wp: hoare_drop_imps ksReadyQueuesL1Bitmap_return_wp)+
  done

crunch isHighestPrio
  for inv[wp]: P
crunch curDomain
  for inv[wp]: P
crunch scheduleSwitchThreadFastfail
  for inv[wp]: P

lemma setSchedulerAction_invs': (* not in wp set, clobbered by ssa_wp *)
  "setSchedulerAction ChooseNewThread \<lbrace>invs' \<rbrace>"
  by (wpsimp simp: invs'_def cur_tcb'_def valid_state'_def valid_irq_node'_def ct_not_inQ_def
                   ct_idle_or_in_cur_domain'_def)

lemma thread_get_when_corres:
  assumes x: "\<And>tcb tcb'. tcb_relation tcb tcb' \<Longrightarrow> r (f tcb) (f' tcb')"
  shows      "corres (\<lambda>rv rv'. b \<longrightarrow> r rv rv') (tcb_at t and pspace_aligned and pspace_distinct) (tcb_at' t)
                ((if b then thread_get f t else return 0)) (threadGet f' t)"
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply (rule corres_guard_imp, rule threadGet_corres; simp add: x)
  apply (clarsimp simp: threadGet_def)
  apply (rule corres_noop)
  apply wpsimp+
  done

lemma tcb_sched_enqueue_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_enqueue t \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def tcb_sched_enqueue_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def obj_at_def etcb_at_def is_etcb_at_def etcbs_of'_def)
  done

lemma tcb_sched_append_in_correct_ready_q[wp]:
  "tcb_sched_action tcb_sched_append tcb_ptr \<lbrace>in_correct_ready_q\<rbrace> "
  unfolding tcb_sched_action_def tcb_sched_append_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: in_correct_ready_q_def obj_at_def etcb_at_def is_etcb_at_def etcbs_of'_def)
  done

lemma tcb_sched_enqueue_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_enqueue t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def etcb_at_def is_etcb_at_def)
  done

lemma tcb_sched_append_ready_qs_distinct[wp]:
  "tcb_sched_action tcb_sched_append t \<lbrace>ready_qs_distinct\<rbrace> "
  unfolding tcb_sched_action_def tcb_sched_append_def set_tcb_queue_def
  apply (wpsimp wp: thread_get_wp')
  apply (clarsimp simp: ready_qs_distinct_def etcb_at_def is_etcb_at_def)
  done

crunch set_scheduler_action
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (wp: crunch_wps simp: in_correct_ready_q_def ready_qs_distinct_def)

crunch reschedule_required
  for in_correct_ready_q[wp]: in_correct_ready_q
  and ready_qs_distinct[wp]: ready_qs_distinct
  (ignore: tcb_sched_action wp: crunch_wps)

locale Schedule_R_3 = Schedule_R_2 +
  assumes scheduleChooseNewThread_corres:
    "corres dc
       (\<lambda>s. invs s \<and> valid_domain_list s \<and> valid_sched s \<and> scheduler_action s = choose_new_thread)
       (\<lambda>s. invs' s \<and> ksSchedulerAction s = ChooseNewThread)
       schedule_choose_new_thread scheduleChooseNewThread"
  assumes scheduleChooseNewThread_invs':
    "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
     scheduleChooseNewThread
     \<lbrace>\<lambda>_. invs' \<rbrace>"
  assumes scheduleChooseNewThread_ct_activatable'[wp]:
    "\<lbrace> invs' and (\<lambda>s. ksSchedulerAction s = ChooseNewThread) \<rbrace>
     scheduleChooseNewThread
     \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
begin

lemma schedule_corres:
  "corres dc (invs and valid_domain_list and valid_sched and valid_list) invs'
          (Schedule_A.schedule) ThreadDecls_H.schedule"
  supply ssa_wp[wp del]
  supply tcbSchedEnqueue_invs'[wp del]
  supply tcbSchedEnqueue_invs'_not_ResumeCurrentThread[wp del]
  supply setSchedulerAction_direct[wp]
  supply if_split[split del]

  apply (clarsimp simp: Schedule_A.schedule_def Thread_H.schedule_def)
  apply (subst thread_get_test)
  apply (subst thread_get_comm)
  apply (subst schact_bind_inside)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getCurThread_corres[THEN corres_rel_imp[where r="\<lambda>x y. y = x"],simplified]])
      apply (rule corres_split[OF getSchedulerAction_corres])
        apply (rule corres_split_sched_act,assumption)
          apply (rule_tac P="tcb_at ct" in corres_symb_exec_l')
            apply (rule_tac corres_symb_exec_l)
               apply simp
               apply (rule corres_assert_ret)
              apply ((wpsimp wp: thread_get_wp' gets_exs_valid)+)
         prefer 2
         (* choose thread *)
         apply clarsimp
         apply (rule corres_split[OF thread_get_isRunnable_corres])
           apply (rule corres_split)
              apply (rule corres_when, simp)
              apply (rule tcbSchedEnqueue_corres, simp)
             apply (rule scheduleChooseNewThread_corres, simp)
            apply (wp thread_get_wp' tcbSchedEnqueue_invs' hoare_vcg_conj_lift hoare_drop_imps
                      valid_domain_list_lift
                   | clarsimp)+
        (* switch to thread: the policy picks, so the candidate is only appended *)
        apply (rule corres_split[OF thread_get_isRunnable_corres],
                rename_tac was_running wasRunning)
          apply (rule corres_split)
             apply (rule corres_when, simp)
             apply (rule tcbSchedEnqueue_corres, simp)
            apply (rule corres_split[OF tcbSchedAppend_corres], simp)
              apply (simp, fold dc_def)
              apply (rule corres_split)
                 apply (rule setSchedulerAction_corres; simp)
                apply (rule scheduleChooseNewThread_corres)
               apply (wp valid_domain_list_lift | simp)+
               apply (simp add: valid_sched_def)
               apply wp
               apply (rule hoare_vcg_conj_lift)
                apply (rule_tac t=t in set_scheduler_action_cnt_valid_blocked')
               apply (wpsimp wp: setSchedulerAction_invs' valid_domain_list_lift)+
             apply (wp tcb_sched_action_append_valid_blocked hoare_vcg_all_lift append_thread_queued)
            apply (wp tcbSchedAppend_invs'_not_ResumeCurrentThread)
           apply (clarsimp simp: conj_commute conj_left_commute cong: conj_cong)
           apply (wp valid_domain_list_lift)
           apply (rule_tac Q'="\<lambda>_ s. valid_blocked_except t s \<and> scheduler_action s = switch_thread t"
                    in hoare_post_imp, fastforce)
           apply (wp add: tcb_sched_action_enqueue_valid_blocked_except
                          tcbSchedEnqueue_invs'_not_ResumeCurrentThread thread_get_wp
                     del: gets_wp
                  | strengthen valid_objs'_valid_tcbs')+
       apply (clarsimp simp: if_apply_def2 cong: imp_cong conj_cong)
       apply (wp gets_wp)+

   (* abstract final subgoal *)
   apply clarsimp

   subgoal for s
     apply (clarsimp split: Structures_A.scheduler_action.splits
                     simp: invs_psp_aligned invs_distinct invs_valid_objs invs_arch_state
                           invs_vspace_objs[simplified] tcb_at_invs)
     apply (rule conjI, clarsimp)
      apply (fastforce simp: invs_def
                            valid_sched_def valid_sched_action_def is_activatable_def
                            st_tcb_at_def obj_at_def valid_state_def only_idle_def
                            )
     apply (rule conjI, clarsimp)
      subgoal for candidate
        apply (clarsimp simp: valid_sched_def invs_def valid_state_def cur_tcb_def
                               valid_sched_action_def weak_valid_sched_action_def
                               valid_blocked_except_def valid_blocked_def invs_hyp_sym_refs)
        apply (fastforce simp add: pred_tcb_at_def obj_at_def is_tcb valid_idle_def)
        done
     (* choose new thread case *)
     apply (intro impI conjI allI tcb_at_invs
            | fastforce simp: invs_def cur_tcb_def
                              valid_sched_def  st_tcb_at_def obj_at_def valid_state_def
                              weak_valid_sched_action_def not_cur_thread_def)+
     done

  (* haskell final subgoal *)
  apply (clarsimp simp: if_apply_def2 invs'_def valid_state'_def
                  cong: imp_cong  split: scheduler_action.splits)
  apply (fastforce simp: cur_tcb'_def valid_pspace'_def)
  done

end (* Schedule_R_3 *)

lemma ssa_all_invs_but_ct_not_inQ':
  "\<lbrace>all_invs_but_ct_not_inQ' and sch_act_wf sa and
   (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. all_invs_but_ct_not_inQ'\<rbrace>"
proof -
  show ?thesis
    apply (simp add: setSchedulerAction_def)
    apply wp
    apply (clarsimp simp add: invs'_def valid_state'_def cur_tcb'_def
                              state_refs_of'_def ps_clear_def valid_irq_node'_def
                              tcb_in_cur_domain'_def ct_idle_or_in_cur_domain'_def bitmapQ_defs
                        cong: option.case_cong)
    done
qed

lemma ssa_ct_not_inQ:
  "\<lbrace>\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. ct_not_inQ\<rbrace>"
  by (simp add: setSchedulerAction_def ct_not_inQ_def, wp, clarsimp)

lemma ssa_all_invs_but_ct_not_inQ''[simplified]:
  "\<lbrace>\<lambda>s. (all_invs_but_ct_not_inQ' s \<and> sch_act_wf sa s)
    \<and> (sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s)
    \<and> (sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp only: all_invs_but_not_ct_inQ_check' [symmetric])
  apply (rule hoare_elim_pred_conj)
  apply (wp hoare_vcg_conj_lift [OF ssa_all_invs_but_ct_not_inQ' ssa_ct_not_inQ])
  apply (clarsimp)
  done

lemma ssa_invs':
  "\<lbrace>invs' and sch_act_wf sa and
    (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s) and
    (\<lambda>s. sa = ResumeCurrentThread \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s)\<rbrace>
   setSchedulerAction sa \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp ssa_all_invs_but_ct_not_inQ'')
  apply (clarsimp simp add: invs'_def valid_state'_def)
  done

lemma getDomainTime_wp[wp]: "\<lbrace>\<lambda>s. P (ksDomainTime s) s \<rbrace> getDomainTime \<lbrace> P \<rbrace>"
  unfolding getDomainTime_def
  by wp

lemma switchToThread_ct_not_queued_2:
  "\<lbrace>invs_no_cicd' and tcb_at' t\<rbrace> switchToThread t \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
  (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (simp add: Thread_H.switchToThread_def)
  apply (wp)
    apply (simp add: switchToThread_def setCurThread_def)
    apply (wp tcbSchedDequeue_not_tcbQueued hoare_drop_imp | simp)+
  done

lemma setCurThread_obj_at':
  "\<lbrace> obj_at' P t \<rbrace> setCurThread t \<lbrace>\<lambda>rv s. obj_at' P (ksCurThread s) s \<rbrace>"
proof -
  show ?thesis
    apply (simp add: setCurThread_def)
    apply wp
    apply (simp add: ct_in_state'_def st_tcb_at'_def)
    done
qed

context Schedule_R begin

lemma switchToIdleThread_ct_not_queued_no_cicd':
  "\<lbrace>invs_no_cicd'\<rbrace> switchToIdleThread \<lbrace>\<lambda>_ s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<rbrace>"
  unfolding switchToIdleThread_def
  apply (wpsimp wp: setCurThread_obj_at' simp: ready_qs_runnable_def)
  apply (drule_tac x="ksIdleThread s" in spec)
  apply (clarsimp simp: invs_no_cicd'_def valid_idle'_def st_tcb_at'_def idle_tcb'_def obj_at'_def)
  done

lemma switchToThread_tcb_in_cur_domain':
  "\<lbrace>tcb_in_cur_domain' thread\<rbrace>
   ThreadDecls_H.switchToThread thread
   \<lbrace>\<lambda>y s. tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (simp add: Thread_H.switchToThread_def setCurThread_def)
  apply (wpsimp wp: tcbSchedDequeue_not_tcbQueued hoare_drop_imps)
  done

lemma inQ_opt_pred_obj_at':
  "\<lbrakk>(inQ d p |< tcbs_of' s) t; pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> obj_at' (inQ d p) t s"
  by (fastforce intro: aligned'_distinct'_ko_wp_at'I
                 simp: obj_at'_real_def opt_map_def opt_pred_def split: option.splits)

text \<open>
  Every member of the highest-priority ready queue is queued with that priority and domain and is
  runnable. This generalises @{thm lookupBitmapPriority_obj_at'}, which is the same statement for the
  head only.
\<close>
lemma lookupBitmapPriority_member_obj_at':
  "\<lbrakk>ksReadyQueuesL1Bitmap s d \<noteq> 0; valid_bitmapQ s; bitmapQ_no_L1_orphans s;
    ksReadyQueues_asrt s; ready_qs_runnable s; pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> (\<forall>t \<in> set (oqueueQueueList s (ksReadyQueues s (d, lookupBitmapPriority d s))).
          obj_at' (inQ d (lookupBitmapPriority d s) and runnable' \<circ> tcbState) t s)
       \<and> oqueueQueueList s (ksReadyQueues s (d, lookupBitmapPriority d s)) \<noteq> []"
  apply (drule (2) bitmapQ_from_bitmap_lookup)
  apply (simp add: valid_bitmapQ_bitmapQ_simp)
  apply (clarsimp simp: ready_queue_relation_def ksReadyQueues_asrt_def tcbQueueEmpty_def)
  apply (drule_tac x=d in spec)
  apply (drule_tac x="lookupBitmapPriority d s" in spec)
  apply clarsimp
  apply (rename_tac ts)
  apply (frule oqueueQueueList_eq)
  apply (intro conjI)
   apply (clarsimp simp: obj_at'_and)
   apply (drule_tac x=t in spec)
   apply clarsimp
   apply (frule (2) inQ_opt_pred_obj_at')
   apply (fastforce simp: ready_qs_runnable_def obj_at'_def st_tcb_at'_def inQ_def)
  apply (fastforce dest: list_queue_relation_Nil simp: tcbQueueEmpty_def headEndPtrsEmpty_def)
  done

lemma lookupBitmapPriority_sel_exists:
  "\<lbrakk>ksReadyQueuesL1Bitmap s d \<noteq> 0; valid_bitmapQ s; bitmapQ_no_L1_orphans s;
    ksReadyQueues_asrt s; ready_qs_runnable s; pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> \<exists>t. oqueue_sel_conc s (ksReadyQueues s (d, lookupBitmapPriority d s)) = Some t"
  apply (frule (6) lookupBitmapPriority_member_obj_at')
  apply (erule conjE)
  apply (cases "oqueueQueueList s (ksReadyQueues s (d, lookupBitmapPriority d s))"; simp)
  apply (rename_tac t0 ts)
  apply (rule_tac t=t0 and ts=ts in oqueue_sel_conc_Some)
   apply simp
  apply (fastforce simp: st_tcb_at'_def obj_at'_def)
  done

lemma chooseThread_invs_no_cicd'_posts: (* generic version *)
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread
   \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s \<and>
           ct_in_state' activatable' s \<and>
           (ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s) \<rbrace>"
    (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
proof -
  note switchToThread_invs[wp del]
  note switchToThread_invs_no_cicd'[wp del]
  note switchToThread_lookupBitmapPriority_wp[wp]
  note assert_wp[wp del]
  note oqueueSelect_all_wp[wp del]
  note oqueueSelect_inv[wp del]
  note if_split[split del]

  (* if we only have one domain, we are in it *)
  have one_domain_case:
    "\<And>s. \<lbrakk> invs_no_cicd' s; numDomains \<le> 1 \<rbrakk> \<Longrightarrow> ksCurDomain s = 0"
    by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def maxDomain_def)

  show ?thesis
    apply (clarsimp simp: chooseThread_def Let_def curDomain_def)
    apply (rule bind_wp[OF _ stateAssert_sp])+
    apply (rule bind_wp[where Q'="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s
                                              \<and> ksReadyQueues_asrt s \<and> ready_qs_runnable s"])
     apply (rule_tac Q'="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                                rv = ksReadyQueuesL1Bitmap s curdom \<and>
                                ksReadyQueues_asrt s \<and> ready_qs_runnable s" in bind_wp)
      apply (rename_tac l1)
      apply (case_tac "l1 = 0")
       (* switch to idle thread *)
       apply simp
       apply (rule hoare_pre)
        apply (wp (once) switchToIdleThread_ct_not_queued_no_cicd')
        apply (wp (once))
        apply ((wp hoare_disjI1 switchToIdleThread_curr_is_idle)+)[1]
       apply simp
      (* we have a thread to switch to *)
      apply (clarsimp simp: bitmap_fun_defs)
      apply (wp assert_inv switchToThread_ct_not_queued_2 hoare_disjI2
                switchToThread_tcb_in_cur_domain' oqueueSelect_mem_wp)
      apply (clarsimp simp:  all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def
                             valid_bitmaps_def)
      apply (frule (6) lookupBitmapPriority_obj_at')
      apply (frule (6) lookupBitmapPriority_member_obj_at')
      apply (frule (6) lookupBitmapPriority_sel_exists)
      apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def tcbQueueEmpty_def inQ_def)
      apply (intro conjI ballI; (drule (1) bspec)?; fastforce)
     apply (wpsimp simp: bitmap_fun_defs curDomain_def one_domain_case)+
    done
qed

lemma chooseThread_activatable_2:
  "\<lbrace>invs_no_cicd'\<rbrace> chooseThread \<lbrace>\<lambda>rv. ct_in_state' activatable'\<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs_no_cicd'_posts)
   apply simp+
  done

lemma chooseThread_ct_not_queued_2:
  "\<lbrace> invs_no_cicd'\<rbrace> chooseThread \<lbrace>\<lambda>rv s. obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s\<rbrace>"
    (is "\<lbrace>_\<rbrace> _ \<lbrace>\<lambda>_. ?POST\<rbrace>")
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs_no_cicd'_posts)
   apply simp+
  done

lemma chooseThread_invs_no_cicd':
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread \<lbrace>\<lambda>rv. invs' \<rbrace>"
proof -
  note switchToThread_invs[wp del]
  note switchToThread_invs_no_cicd'[wp]
  note switchToThread_lookupBitmapPriority_wp[wp del]
  note assert_wp[wp del]
  note oqueueSelect_all_wp[wp del]
  note oqueueSelect_inv[wp del]
  note if_split[split del]

  (* if we only have one domain, we are in it *)
  have one_domain_case:
    "\<And>s. \<lbrakk> invs_no_cicd' s; numDomains \<le> 1 \<rbrakk> \<Longrightarrow> ksCurDomain s = 0"
    by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def maxDomain_def)

  (* NOTE: do *not* unfold numDomains in the rest of the proof,
           it should work for any number *)

  (* FIXME this is almost identical to the chooseThread_invs_no_cicd'_posts proof, can generalise? *)
  show ?thesis
    apply (clarsimp simp: chooseThread_def Let_def curDomain_def)
    apply (rule bind_wp[OF _ stateAssert_sp])+
    apply (rule bind_wp[where Q'="\<lambda>rv s. invs_no_cicd' s \<and> rv = ksCurDomain s
                                              \<and> ksReadyQueues_asrt s \<and> ready_qs_runnable s"])
     apply (rule_tac Q'="\<lambda>rv s. invs_no_cicd' s \<and> curdom = ksCurDomain s \<and>
                                rv = ksReadyQueuesL1Bitmap s curdom \<and>
                                ksReadyQueues_asrt s \<and> ready_qs_runnable s" in bind_wp)
      apply (rename_tac l1)
      apply (case_tac "l1 = 0")
       (* switch to idle thread *)
       apply (simp, wp switchToIdleThread_invs_no_cicd', simp)
      (* we have a thread to switch to *)
      apply (clarsimp simp: bitmap_fun_defs)
      apply (wp assert_inv oqueueSelect_mem_wp)
      apply (clarsimp simp:  all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def
                             valid_bitmaps_def)
      apply (frule (6) lookupBitmapPriority_obj_at')
      apply (frule (6) lookupBitmapPriority_member_obj_at')
      apply (frule (6) lookupBitmapPriority_sel_exists)
      apply (clarsimp simp: tcb_in_cur_domain'_def obj_at'_def tcbQueueEmpty_def inQ_def)
      apply (intro conjI ballI; (drule (1) bspec)?; fastforce)
     apply (wpsimp simp: bitmap_fun_defs curDomain_def one_domain_case)+
    done
qed

lemma chooseThread_in_cur_domain':
  "\<lbrace> invs_no_cicd' \<rbrace> chooseThread \<lbrace>\<lambda>rv s. ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s\<rbrace>"
  apply (rule hoare_pre, rule hoare_strengthen_post)
    apply (rule chooseThread_invs_no_cicd'_posts, simp_all)
  done

end (* Schedule_R *)

crunch setCurThread
  for nosch: "\<lambda>s. P (ksSchedulerAction s)"

lemma (in Schedule_R_3) schedule_invs':
  "\<lbrace>invs'\<rbrace> ThreadDecls_H.schedule \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply ssa_wp[wp del]
  apply (simp add: schedule_def)
  apply (rule_tac bind_wp, rename_tac t)
   apply (wp, wpc)
      \<comment> \<open>action = ResumeCurrentThread\<close>
      apply (wp)[1]
     \<comment> \<open>action = ChooseNewThread\<close>
     apply (wp scheduleChooseNewThread_invs')
    \<comment> \<open>action = SwitchToThread candidate\<close>
    apply (wpsimp wp: scheduleChooseNewThread_invs' ssa_invs' setSchedulerAction_invs'
                      tcbSchedAppend_invs'_not_ResumeCurrentThread
                      tcbSchedEnqueue_invs'_not_ResumeCurrentThread setSchedulerAction_direct
                      switchToThread_tcb_in_cur_domain' switchToThread_ct_not_queued_2
           | wp hoare_disjI2[where Q'="\<lambda>_ s. tcb_in_cur_domain' (ksCurThread s) s"]
           | wp hoare_drop_imp[where f="isHighestPrio d p" for d p]
           | simp only: obj_at'_activatable_st_tcb_at'[simplified comp_def]
           | strengthen invs'_invs_no_cicd
           | wp hoare_vcg_imp_lift)+
  apply (frule invs_sch_act_wf')
  apply (auto simp: invs_sch_act_wf' obj_at'_activatable_st_tcb_at'
                     st_tcb_at'_runnable_is_activatable)
  done

lemma schedule_sch:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv s. ksSchedulerAction s = ResumeCurrentThread\<rbrace>"
  by (wp setSchedulerAction_direct | wpc| simp add: schedule_def scheduleChooseNewThread_def)+

lemma schedule_sch_act_simple:
  "\<lbrace>\<top>\<rbrace> schedule \<lbrace>\<lambda>rv. sch_act_simple\<rbrace>"
  apply (rule hoare_strengthen_post [OF schedule_sch])
  apply (simp add: sch_act_simple_def)
  done

lemma ssa_ct:
  "\<lbrace>ct_in_state' P\<rbrace> setSchedulerAction sa \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
proof -
  show ?thesis
    apply (unfold setSchedulerAction_def)
    apply wp
    apply (clarsimp simp add: ct_in_state'_def pred_tcb_at'_def)
    done
qed

lemma (in Schedule_R_3) schedule_ct_activatable'[wp]:
  "\<lbrace>invs'\<rbrace> ThreadDecls_H.schedule \<lbrace>\<lambda>_. ct_in_state' activatable'\<rbrace>"
  supply ssa_wp[wp del]
  apply (simp add: schedule_def)
  apply (rule_tac bind_wp, rename_tac t)
   apply (wp, wpc)
      \<comment> \<open>action = ResumeCurrentThread\<close>
      apply (wp)[1]
     \<comment> \<open>action = ChooseNewThread\<close>
     apply wpsimp
    \<comment> \<open>action = SwitchToThread\<close>
    apply (wpsimp wp: ssa_invs' setSchedulerAction_direct ssa_ct scheduleChooseNewThread_ct_activatable'
                      tcbSchedAppend_invs'_not_ResumeCurrentThread
                      tcbSchedEnqueue_invs'_not_ResumeCurrentThread
           | wp hoare_drop_imp[where f="isHighestPrio d p" for d p]
           | simp only: obj_at'_activatable_st_tcb_at'[simplified comp_def]
           | strengthen invs'_invs_no_cicd
           | wp hoare_vcg_imp_lift)+
  apply (fastforce dest: invs_sch_act_wf' elim: pred_tcb'_weakenE
                   simp: sch_act_wf obj_at'_activatable_st_tcb_at')
  done

lemma threadSet_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> threadSet f t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  by (wp sch_act_sane_lift)

lemma rescheduleRequired_sch_act_sane[wp]:
  "\<lbrace>\<top>\<rbrace> rescheduleRequired \<lbrace>\<lambda>rv. sch_act_sane\<rbrace>"
  apply (simp add: rescheduleRequired_def sch_act_sane_def
                   setSchedulerAction_def)
  by (wp | wpc | clarsimp)+

lemma setSchedulerAction_ChooseNewThread_sch_act_sane[wp]:
  "\<lbrace>\<top>\<rbrace> setSchedulerAction ChooseNewThread \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (wp ssa_wp)
  by (clarsimp simp: sch_act_sane_def)

lemma sts_sch_act_sane:
  "setThreadState st t \<lbrace>sch_act_sane\<rbrace>"
  apply (simp add: setThreadState_def)
  including no_pre
  apply (wp hoare_drop_imps
           | simp add: threadSet_sch_act_sane)+
  done

lemma sbn_sch_act_sane:
  "\<lbrace>sch_act_sane\<rbrace> setBoundNotification ntfn t \<lbrace>\<lambda>_. sch_act_sane\<rbrace>"
  apply (simp add: setBoundNotification_def)
  apply (wp | simp add: threadSet_sch_act_sane)+
  done

crunch rescheduleRequired
  for sym_heap_sched_pointers[wp]: sym_heap_sched_pointers
  and valid_sched_pointers[wp]: valid_sched_pointers

lemma possibleSwitchTo_corres:
  "corres dc
     (weak_valid_sched_action and cur_tcb and st_tcb_at runnable t
      and in_correct_ready_q and ready_qs_distinct and pspace_aligned and pspace_distinct)
     ((\<lambda>s. weak_sch_act_wf (ksSchedulerAction s) s)
      and sym_heap_sched_pointers and valid_sched_pointers and valid_objs')
     (possible_switch_to t) (possibleSwitchTo t)"
  apply (rule_tac Q'=pspace_aligned' in corres_cross_add_guard)
   apply (fastforce dest: pspace_aligned_cross)
  apply (rule_tac Q'=pspace_distinct' in corres_cross_add_guard)
   apply (fastforce dest: pspace_distinct_cross)
  apply (rule corres_cross_over_guard[where P'=Q and Q="tcb_at' t and Q" for Q])
   apply (clarsimp simp: state_relation_def)
   apply (rule tcb_at_cross, erule st_tcb_at_tcb_at; assumption)
  apply (simp add: possible_switch_to_def possibleSwitchTo_def cong: if_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF curDomain_corres], simp)
      apply (rule corres_split)
         apply (rule threadGet_corres[where r="(=)"])
         apply (clarsimp simp: tcb_relation_def)
        apply (rule corres_split[OF getSchedulerAction_corres])
          apply (rule corres_if, simp)
           apply (rule tcbSchedEnqueue_corres, simp)
          apply (rule corres_if, simp)
            apply (case_tac action; simp)
           apply (rule corres_split[OF rescheduleRequired_corres])
             apply (rule tcbSchedEnqueue_corres, simp)
            apply (wp reschedule_required_valid_queues | strengthen valid_objs'_valid_tcbs')+
          apply (rule setSchedulerAction_corres, simp)
         apply (wpsimp wp: hoare_drop_imps)+
   apply (clarsimp simp: st_tcb_at_tcb_at)
  apply fastforce
  done

end
