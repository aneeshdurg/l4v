(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Scheduler"

theory Schedule_A
imports Arch_A
begin

arch_requalify_consts (A)
  arch_switch_to_thread
  arch_switch_to_idle_thread
  arch_prepare_next_domain

abbreviation
  "idle st \<equiv> st = Structures_A.IdleThreadState"

text \<open>Switches the current thread to the specified one.\<close>
definition
  switch_to_thread :: "obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "switch_to_thread t \<equiv> do
     state \<leftarrow> get;
     assert (get_tcb t state \<noteq> None);
     arch_switch_to_thread t;
     tcb_sched_action (tcb_sched_dequeue) t;
     modify (\<lambda>s. s \<lparr> cur_thread := t \<rparr>)
   od"

text \<open>Asserts that a thread is runnable before switching to it.\<close>
definition guarded_switch_to :: "obj_ref \<Rightarrow> (unit, 'z::state_ext) s_monad" where
  "guarded_switch_to thread \<equiv> do
     ts \<leftarrow> get_thread_state thread;
     assert (runnable ts);
     switch_to_thread thread
    od"

text \<open>Switches to the idle thread.\<close>
definition
  switch_to_idle_thread :: "(unit,'z::state_ext) s_monad" where
  "switch_to_idle_thread \<equiv> do
     thread \<leftarrow> gets idle_thread;
     arch_switch_to_idle_thread;
     modify (\<lambda>s. s \<lparr> cur_thread := thread \<rparr>)
   od"

definition domain_end_marker :: "domain \<times> domain_duration" where
  "domain_end_marker = (0, 0)"

definition
  next_domain :: "(unit, 'z::state_ext) s_monad" where
  "next_domain \<equiv> do
    modify (\<lambda>s.
      let index_inc = domain_index s + 1;
          index' = if domain_list s ! index_inc = domain_end_marker
                   then domain_start_index s
                   else index_inc;
          dom_entry = domain_list s ! index'
      in s\<lparr> domain_index := index',
            cur_domain := fst dom_entry,
            domain_time := ucast (snd dom_entry)\<rparr>);
    do_extended_op $ modify (\<lambda>s. s \<lparr>work_units_completed := 0\<rparr>)
  od"

definition
  dec_domain_time :: "(unit, 'z::state_ext) s_monad" where
  "dec_domain_time = modify (\<lambda>s. s\<lparr>domain_time := domain_time s - 1\<rparr>)"

definition max_non_empty_queue :: "(priority \<Rightarrow> ready_queue) \<Rightarrow> ready_queue" where
  "max_non_empty_queue queues \<equiv> queues (Max {prio. queues prio \<noteq> []})"

definition oqueue_remaining_budget ::
  "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> ticks option"
where
  "oqueue_remaining_budget s t \<equiv>
    case get_tcb t s of
      None \<Rightarrow> None
    | Some tcb \<Rightarrow>
        if runnable (tcb_state tcb) then
          let pending = (if tcb_sched_context tcb = Some (cur_sc s)
                         then consumed_time s else 0);
              budget = tcb_oqueue_budget tcb
          in Some (if budget < pending then 0 else budget - pending)
        else None"

function oqueue_best ::
  "'z::state_ext state \<Rightarrow> ready_queue \<Rightarrow> (obj_ref \<times> ticks) option"
where
  "oqueue_best s [] = None"
| "oqueue_best s (t # ts) =
    (case oqueue_remaining_budget s t of
       None \<Rightarrow> oqueue_best s ts
     | Some budget \<Rightarrow>
         (case oqueue_best s ts of
            None \<Rightarrow> Some (t, budget)
          | Some (best, best_budget) \<Rightarrow>
              if budget \<le> best_budget then Some (t, budget)
              else Some (best, best_budget)))"
  by pat_completeness auto
termination by lexicographic_order

definition oqueue_select ::
  "'z::state_ext state \<Rightarrow> ready_queue \<Rightarrow> obj_ref option"
where
  "oqueue_select s queue \<equiv>
    case oqueue_best s queue of None \<Rightarrow> None | Some (t, _) \<Rightarrow> Some t"
lemma oqueue_best_in_queue:
  "oqueue_best s q = Some (t, b) \<Longrightarrow>
   t \<in> set q \<and> (\<exists>tcb. get_tcb t s = Some tcb \<and> runnable (tcb_state tcb))"
proof (induction q arbitrary: t b)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
    using Cons.prems Cons.IH
    by (fastforce simp: oqueue_remaining_budget_def Let_def
                  split: option.splits prod.splits if_splits)
qed

lemma oqueue_best_not_None:
  "\<lbrakk>q \<noteq> []; \<forall>t \<in> set q. \<exists>tcb. get_tcb t s = Some tcb \<and> runnable (tcb_state tcb)\<rbrakk>
   \<Longrightarrow> oqueue_best s q \<noteq> None"
  by (cases q;
      fastforce simp: oqueue_remaining_budget_def Let_def
                split: option.splits prod.splits if_splits)

lemma oqueue_select_in_queue:
  "oqueue_select s q = Some t \<Longrightarrow>
   t \<in> set q \<and> (\<exists>tcb. get_tcb t s = Some tcb \<and> runnable (tcb_state tcb))"
  by (fastforce simp: oqueue_select_def dest: oqueue_best_in_queue split: option.splits)

lemma oqueue_select_not_None:
  "\<lbrakk>q \<noteq> []; \<forall>t \<in> set q. \<exists>tcb. get_tcb t s = Some tcb \<and> runnable (tcb_state tcb)\<rbrakk>
   \<Longrightarrow> oqueue_select s q \<noteq> None"
  by (fastforce simp: oqueue_select_def dest: oqueue_best_not_None split: option.splits)

definition attach_oqueue_policy :: "(bool, 'z::state_ext) s_monad" where
  "attach_oqueue_policy \<equiv> do
     active \<leftarrow> gets oqueue_active;
     if active then return False
     else do
       modify (\<lambda>s. s\<lparr>oqueue_active := True\<rparr>);
       return True
     od
   od"

definition detach_oqueue_policy :: "(bool, 'z::state_ext) s_monad" where
  "detach_oqueue_policy \<equiv> do
     active \<leftarrow> gets oqueue_active;
     if active then do
       modify (\<lambda>s. s\<lparr>oqueue_active := False\<rparr>);
       return True
     od else return False
   od"


definition choose_thread :: "(unit, 'z::state_ext) s_monad" where
  "choose_thread \<equiv> do
     d \<leftarrow> gets cur_domain;
     queues \<leftarrow> gets (\<lambda>s. ready_queues s d);
     if \<forall>prio. queues prio = []
     then switch_to_idle_thread
     else do
       active \<leftarrow> gets oqueue_active;
       if active then do
         s \<leftarrow> get;
         candidate \<leftarrow> return (oqueue_select s (max_non_empty_queue queues));
         assert (candidate \<noteq> None);
         guarded_switch_to (the candidate)
       od else guarded_switch_to (hd (max_non_empty_queue queues))
     od
   od"

text \<open>
  Determine whether given priority is highest among queued ready threads in given domain.
  Trivially true if no threads are ready.\<close>
definition
  is_highest_prio :: "domain \<Rightarrow> priority \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "is_highest_prio d p s \<equiv>
    (\<forall>prio. ready_queues s d prio = [])
    \<or> p \<ge> Max {prio. ready_queues s d prio \<noteq> []}"

definition
  "schedule_switch_thread_fastfail ct it ct_prio target_prio \<equiv>
     return $ ct \<noteq> it \<longrightarrow> target_prio < ct_prio"

definition
  "schedule_choose_new_thread \<equiv> do
     dom_time \<leftarrow> gets domain_time;
     when (dom_time = 0) $ do
       arch_prepare_next_domain;
       next_domain
     od;
     choose_thread;
     set_scheduler_action resume_cur_thread
   od"

definition
  "schedule \<equiv> do
     ct \<leftarrow> gets cur_thread;
     ct_st \<leftarrow> get_thread_state ct;
     ct_runnable \<leftarrow> return $ runnable ct_st;
     action \<leftarrow> gets scheduler_action;
     (case action
       of resume_cur_thread \<Rightarrow> do
            id \<leftarrow> gets idle_thread;
            assert (ct_runnable \<or> ct = id);
            return ()
         od
       | choose_new_thread \<Rightarrow> do
           when ct_runnable (tcb_sched_action tcb_sched_enqueue ct);
           schedule_choose_new_thread
         od
       | switch_thread candidate \<Rightarrow> do
           when ct_runnable (tcb_sched_action tcb_sched_enqueue ct);

           it \<leftarrow> gets idle_thread;
           target_prio \<leftarrow> thread_get tcb_priority candidate;

           \<comment> \<open>Infoflow does not like asking about the idle thread's priority or domain.\<close>
           ct_prio \<leftarrow> if ct \<noteq> it then thread_get tcb_priority ct else return 0;
           \<comment> \<open>When to look at the bitmaps. This optimisation is used in the C fast path,
              but there we know @{text cur_thread} is not idle.\<close>
           fastfail \<leftarrow> schedule_switch_thread_fastfail ct it ct_prio target_prio;

           cur_dom \<leftarrow> gets cur_domain;
           highest \<leftarrow> gets (is_highest_prio cur_dom target_prio);
           \<comment> \<open>While the OQueue policy is attached, a direct candidate never bypasses the policy:
              it is appended to its queue and the new thread is chosen by @{const choose_thread}.\<close>
           policy_active \<leftarrow> gets oqueue_active;
           if (fastfail \<and> \<not>highest \<and> \<not>policy_active)
           then do
               \<comment> \<open>Candidate is not best candidate, choose a new thread\<close>
               tcb_sched_action tcb_sched_enqueue candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else if ((ct_runnable \<and> ct_prio = target_prio) \<or> policy_active)
           then do
               \<comment> \<open>Current thread was runnable and candidate is not strictly better
                  want current thread to run next, so append the candidate to end of queue
                  and choose again\<close>
               tcb_sched_action tcb_sched_append candidate;
               set_scheduler_action choose_new_thread;
               schedule_choose_new_thread
             od
           else do
             guarded_switch_to candidate;
             \<comment> \<open>Duplication assists in wp proof under different scheduler actions\<close>
             set_scheduler_action resume_cur_thread
           od
        od)
    od"

definition domain_schedule_configure ::
  "nat \<Rightarrow> domain \<Rightarrow> domain_duration \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "domain_schedule_configure index domain duration \<equiv>
     modify (\<lambda>s. s\<lparr> domain_list := (domain_list s) [index := (domain, duration)]\<rparr>)"

definition domain_set_start :: "nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "domain_set_start index \<equiv> do
     modify (\<lambda>s. s\<lparr>domain_start_index := index\<rparr>);
     modify (\<lambda>s. s\<lparr>domain_time := 0\<rparr>);
     \<comment> \<open>Set the index such that after increment in @{const next_domain}, it will point to
         the last domain schedule item, which is reserved to be an end marker.\<close>
     domain_list_len \<leftarrow> gets (length \<circ> domain_list);
     modify (\<lambda>s. s\<lparr>domain_index := domain_list_len - 2\<rparr>);
     reschedule_required
   od"

end
