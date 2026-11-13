(*
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory OQueueHandoff_R
imports Schedule_R
begin

text \<open>
  Attaching and detaching the OQueue policy only writes the flag @{const ksOQueueActive}. The flag
  is Haskell-only state: the abstract specification does not mention it and neither does
  @{const state_relation} or @{const invs'}. So the handoff is correct if (1) it preserves
  @{const invs'}, (2) it preserves the state relation, and (3) the scheduler refines the abstract
  specification whichever value the flag has (@{text chooseThread_corres}, which quantifies over
  the flag).
\<close>

interpretation oqa_update': p_arch_idle_int_cur_update_eq' "ksOQueueActive_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> oqa_update': Arch_p_arch_idle_int_cur_update_eq' "ksOQueueActive_update f" ..

lemma invs'_oqa[simp]:
  "invs' (ksOQueueActive_update f s) = invs' s"
  by (simp add: invs'_def cur_tcb'_def valid_state'_def valid_bitmaps_def
                valid_irq_node'_def valid_machine_state'_def
                ct_not_inQ_def ct_idle_or_in_cur_domain'_def tcb_in_cur_domain'_def
                bitmapQ_defs)

lemma state_relation_oqa[simp]:
  "((s, ksOQueueActive_update f s') \<in> state_relation) = ((s, s') \<in> state_relation)"
  by (simp add: state_relation_def ready_queues_relation_def)

lemma attachOQueuePolicy_invs'[wp]:
  "\<lbrace>invs'\<rbrace> attachOQueuePolicy \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: attachOQueuePolicy_def)

lemma detachOQueuePolicy_invs'[wp]:
  "\<lbrace>invs'\<rbrace> detachOQueuePolicy \<lbrace>\<lambda>_. invs'\<rbrace>"
  by (wpsimp simp: detachOQueuePolicy_def)

lemma attachOQueuePolicy_active:
  "\<lbrace>\<top>\<rbrace> attachOQueuePolicy \<lbrace>\<lambda>_ s. ksOQueueActive s\<rbrace>"
  by (wpsimp simp: attachOQueuePolicy_def)

lemma detachOQueuePolicy_inactive:
  "\<lbrace>\<top>\<rbrace> detachOQueuePolicy \<lbrace>\<lambda>_ s. \<not> ksOQueueActive s\<rbrace>"
  by (wpsimp simp: detachOQueuePolicy_def)

text \<open>Both operations leave everything that does not mention the flag alone.\<close>
lemma attachOQueuePolicy_inv:
  assumes "\<And>f s. P (ksOQueueActive_update f s) = P s"
  shows "\<lbrace>P\<rbrace> attachOQueuePolicy \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: attachOQueuePolicy_def assms)

lemma detachOQueuePolicy_inv:
  assumes "\<And>f s. P (ksOQueueActive_update f s) = P s"
  shows "\<lbrace>P\<rbrace> detachOQueuePolicy \<lbrace>\<lambda>_. P\<rbrace>"
  by (wpsimp simp: detachOQueuePolicy_def assms)

text \<open>
  The abstract specification has no such operation, so attach and detach correspond to doing
  nothing: the state relation survives.
\<close>
lemma attachOQueuePolicy_corres:
  "corres dc \<top> \<top> (return ()) attachOQueuePolicy"
  unfolding attachOQueuePolicy_def getOQueueActive_def
  by (clarsimp simp: corres_underlying_def bind_def gets_def get_def modify_def put_def
                     return_def split_def split: if_splits)

lemma detachOQueuePolicy_corres:
  "corres dc \<top> \<top> (return ()) detachOQueuePolicy"
  unfolding detachOQueuePolicy_def getOQueueActive_def
  by (clarsimp simp: corres_underlying_def bind_def gets_def get_def modify_def put_def
                     return_def split_def split: if_splits)

end
