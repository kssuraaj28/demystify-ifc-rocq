From Stdlib Require List ssreflect ssrfun ssrbool FunctionalExtensionality.
Import List ListNotations ssreflect ssrfun ssrbool FunctionalExtensionality.

From Ltac2 Require Import Ltac2.

Require Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem.
Import Tacs Util VarValStore Attacker Syntax Lattice4pt Semantics TypeSystem Tacs.Cook.

Set Default Proof Mode "Classic".
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".
Set Mangle Names. Set Mangle Names Light.
(* TODO: Order seems to matter. Syntax before fails *)

#[local] Ltac2 mutable this_cookbook_ := create_new_cookbook.
Ltac2 Set this_cookbook_ := create_new_cookbook.

Section cmb_cmd.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.
  (* The simulator state will not be here. I'm doing some big brain intuition*)
  #[local] Set Primitive Projections. (* TODO: All records need to have this? Maybe in prelude? *)

  Record CmbCmd : Type := mk_cmbcmd {
    real_cmd : option Cmd ;
    real_atk_bit : bool ;
    ideal_cmd : option Cmd ;
    pc_lbl : PcLbl ;
  }.

  Fact real_cmd_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (real_cmd (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.

  Fact real_atk_bit_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (real_atk_bit (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.

  Fact ideal_cmd_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (ideal_cmd (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.

  Fact pc_lbl_mk rcmd ratk icmd pclbl :
    ltac2:(cbn_eq (pc_lbl (mk_cmbcmd rcmd ratk icmd pclbl))).
  Proof. done. Qed.
End cmb_cmd.

Section cmb_step.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates : Type}.

  Definition zip (real_cont: list Cmd) (ideal_cont: list Cmd) (atk_steps: nat) (pc_lbl: PcLbl): list CmbCmd :=
    let: real_cont := map Some real_cont in
    let: ideal_cont := map Some ideal_cont in
    let: atk_steps := repeat true atk_steps in
    let: comb := List.combine_extend3 real_cont ideal_cont atk_steps None None false in
    map (fun '(rc, ic, abit) => mk_cmbcmd rc abit ic pc_lbl) comb.


  Section comb_state. 
    #[local] Set Primitive Projections. (* TODO: All records need to have this? Maybe in prelude? *)

    Record CmbState : Type := mk_cmbstate {
      real_store : Store;
      ideal_store : Store;
      sim_store : Store;
      atk_st : AtkStates
    }.

    Definition Cfg := (CmbState * list CmbCmd)%type.
  End comb_state.



Parameter TODO: Store.

  Section step.
    Variable (adv: AdvNextStep AtkStates). 
    Notation AcmdEvent := (Semantics.Event).
    Notation pre_cmd_action := (pre_cmd_action adv).
    Notation post_cmd_action := (post_cmd_action adv).

    Definition cmbcmd_step (c: CmbCmd) (s: CmbState) : Cfg * AcmdEvent :=
      let: mk_cmbcmd real_cmd real_atk_bit ideal_cmd pc_lbl := c in
      let: mk_cmbstate real_st ideal_st sim_st atk_st := s in
    
      (* Corruption first. TODO: When there is endorsement, there will need to be an update to the ideal store as well *)
      let: real_st := if real_atk_bit is false then real_st else pre_cmd_action atk_st real_st in
      let: (real_cnt, real_st, real_event) := (optcmd_stp_cnt real_cmd real_st,  optcmd_stp_store real_cmd real_st, optcmd_evnt real_cmd real_st) in (* TODO: The proof breaks when you update real_st before real_cnt. Why? *)


      let: sim_st := if real_atk_bit is false then sim_st else pre_cmd_action atk_st sim_st in
      (* If pc is secret, then there will not be any change to public vars, so this is okay!    The simulator will not have access to real_cmd in a secret branch *)
      let: sim_st := if (public pc_lbl) is false then sim_st else optcmd_stp_store real_cmd sim_st  in


      (* Controlled ideal corruption. Only a *real* endorse (a public, untrusted
         source — the attacker's PU→PT) corrupts the ideal store; a harmless
         endorse leaves it alone, matching sim_pre. *)
      let: ideal_st :=  if real_cmd isn't  Some (assign (endorse from to)) then ideal_st else
                        if (is_public from && is_untrusted from) is false then ideal_st else
                          update_to_store ideal_st from (sim_st from) in (* get the value of from from sim_st, then update to ideal_st *)
      let: (ideal_cnt, ideal_st) :=  (optcmd_stp_cnt ideal_cmd ideal_st, optcmd_stp_store ideal_cmd ideal_st) in


      (* Controlled ideal read: only a *real* declassify (a secret source made
         public — the ST→PT) reads from the ideal store; a harmless declassify
         (public source) leaves sim alone. The `is_secret from` guard is what
         makes the read sound: a real declassify has a trusted source, so its
         ideal value matches across the trusted views. *)
      let: sim_st := if real_cmd isn't Some (assign (declassify from to)) then sim_st else
                     if (is_secret from && is_public to) is false then sim_st else
                       update_to_store sim_st to (ideal_st to) in (* Controlled ideal read *)
    
    
      let: atk_pst := (post_cmd_action atk_st real_st) in (* Not having this was quite painful. TODO *)
      let: atk_st := if real_atk_bit is false then atk_st else atk_pst.1.1 in
      let: atk_event := if real_atk_bit is false then None else atk_pst.1.2 in
      let: atk_substeps := if real_atk_bit is false then 0 else atk_pst.2 in

      let: new_pc := compute_new_pc_opt pc_lbl real_cmd in
      ((mk_cmbstate real_st ideal_st sim_st atk_st, zip real_cnt ideal_cnt atk_substeps new_pc), mk_acmd_evnt real_event atk_event). 

    Definition cfg_step (cfg: Cfg) : Cfg * AcmdEvent := 
      let: (st, cmdlst) := cfg in
      if cmdlst isn't (cmd :: cmdlst') then (cfg, blank_event) else
      let: (st', cmdlst'', evnt) := cmbcmd_step cmd st in
      (st', cmdlst'' ++ cmdlst', evnt).
  End step.
End cmb_step.


Section inv.
  Import VarValStore.Notations Util.List.

  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable (adv: AdvNextStep AtkStates). 
  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).


  Definition CmbCmdCoreInv '(rcmd,icmd,pclbl) : Prop :=
    pclbl ⊢ rcmd /\ 
    (if (untrusted pclbl) is true 
      then (mk_4ptlbl true true) ⊢ icmd  (* icmd is still a good public untrusted *)
      else rcmd = icmd). (* The rcmd is still well typed *)

  Definition CmbCmdInv (cmb_cmd: CmbCmd) : Prop :=
    let: mk_cmbcmd rcmd _ icmd pclbl := cmb_cmd in (* TODO: is_atk does not make an appearance... *)
    CmbCmdCoreInv (rcmd, icmd, pclbl).

  Definition StateInv (s: CmbState): Prop :=
    let: mk_cmbstate real_st ideal_st sim_st _ := s in
    ⟨ real_st | is_trusted ⟩ = ⟨ ideal_st | is_trusted ⟩ /\
    ⟨ real_st | is_public ⟩ = ⟨ sim_st | is_public ⟩.

  Definition Invariant (c : Cfg): Prop :=
    let: (cmbst, cmdlst) := c in
    Forall CmbCmdInv cmdlst /\
    StateInv cmbst.
End inv.

Section thm.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm}.

  Import VarValStore.Notations Util.List.
   Lemma Forall_CmbCmd_zip:
     forall l1 l2 substeps pc_lbl,
       (* TODO: I didn't have fst and snd before, and that wait painful. How to solve? *)
       Forall (fun p => CmbCmdCoreInv (p.1, p.2, pc_lbl))  (combine_extend2 (map Some l1) (map Some l2) None None) ->
       Forall CmbCmdInv (zip l1 l2 substeps pc_lbl).
   Proof.
     move=> *; rewrite /zip.
     apply/Forall_map/Forall_combine2_ind1;[|eassumption|]=> //= => [[] [] > //|].
     move: (X in if X then _ else _)=> ?; if_easy_goals. (* TODO: Maybe  *)
   Qed.

End thm.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep
    ltac1:(lazymatch goal with
           | |- Forall _ (zip _ _ _ _) => apply/Forall_CmbCmd_zip
           end)
    "Forall_CmbCmd_zip" old.

Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> real_cmd_mk ) "real_cmd_mk" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> real_atk_bit_mk ) "real_atk_bit_mk" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> ideal_cmd_mk) "ideal_cmd_mk" old.
Ltac2 Set this_cookbook_ as old :=
  add_cookstep ltac1:(rewrite -> pc_lbl_mk) "pc_lbl_mk" old.

Ltac2 this_cookbook () := this_cookbook_ ().

Section invprf.
  Import Attacker Util Util.List.
  Context `{!VarPrm, !ValPrm, !AdvLvlPrm, !AdvLeakPrm} {AtkStates: Type}.
  Variable (adv: AdvNextStep AtkStates). 
  Notation CmbState := (CmbState (AtkStates := AtkStates)).
  Notation Cfg := (Cfg (AtkStates := AtkStates)).
  Notation cfg_step := (cfg_step adv).
  Notation cmbcmd_step := (cmbcmd_step adv).

  Section cook.
    Import DecEq DecEq.Notations.
    Import VarValStore.Notations.

    Ltac2 Set curr_cookbook := (fun () => this_cookbook_ ()).
    Ltac2 Set curr_cookbook as old := join_cookbooks Semantics.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks TypeSystem.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Attacker.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Util.List.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks VarValStore.this_cookbook old.
    Ltac2 Set curr_cookbook as old := join_cookbooks Syntax.this_cookbook old.

    Ltac2 Eval print_cookbook curr_cookbook.

    Hint Extern 10 => lazymatch goal with
           |- context [compute_new_pc (mk_4ptlbl true ?p) ?c] =>
              move: ([elaborate compute_new_pc_untr p c])=> [] + ->
           end: core.
    Hint Extern 10 => lazymatch goal with |- _ => apply:step_soundness end: core.

(*    Hint Extern 100 => lazymatch goal with _ =>  cbn end : trickbag. *)

(* TODO 3 debug levels *)
    Ltac2 Set cook_debug := 0. (* TODO: Why can't I access this? *)
    (* TODO: Why does cook make this extremely slow? *)
    (* TODO: Set Ltac Profiling *)

    Lemma cmbcmd_step_inv:
      forall c st,
        CmbCmdInv c ->
        StateInv st ->
        let: ((st', clst'),_) := cmbcmd_step c st in
        StateInv st' /\ Forall CmbCmdInv clst'.
    Proof.
      case; rewrite {}/CmbCmdInv=> - []; cycle 1.
        { move=>>[]_; rewrite/StateInv=> + [].
        case pce: (untrusted _); cycle 1.
        1: move=> <- /= <- *.
        2: move=> * /=. 
        1-2: repeat split; cook.
          { revert_hyp_pat [(option Cmd), (_ ⊢ _)]; case=> /= *; cook. }
        move=> /=. 
        apply/Forall_and; cook; auto with trickbag.
        rewrite-/(WellFormedProg _ _).
        revert_hyp_pat [(option Cmd), (_ ⊢ _)]; case=> /==> [|* //] >.
        apply: step_soundness_pubuntr=> //. } 
      rewrite /CmbCmdCoreInv=> > []; rewrite /(_⊢_)/cmbcmd_step/StateInv=> ? ? [>].
      repeat split; cook.
        { let rcmd := pick_hyp_pat uconstr:(Cmd) in  move: (orbN (is_endorse rcmd))=> /orP [ | noend].
          { move/is_endorse_inv=> [from [to e]]; rewrite -> e in *=> {e}. (* TODO: this branch is longer *)
          revert_hyp_pat (WellFormedCmd _ _)=> /wf_endorse_inv [Hcanon | Hsafe].
          { move: Hcanon=> [Hpc [Hfrom Hto]]; rewrite -> Hpc in *=> {Hpc}.
          have Hg : is_public from && is_untrusted from; [rewrite /is_public /is_untrusted Hfrom // |].
          rewrite Hg.
          revert_hyp_pat (if _ then _ else _)=> /= <- /=.
          apply/storeview_eq_ext=> *; rewrite /clean_assign_stp_store /update_to_store; cook.
          rewrite/get_assign_val/get_assign_dest dec_eq_refl. (* TODO: Eventually this should be a rewrite rule also *)
          case e1: (_ =? _).
          2: case e2: (_ =? _).
          2: apply dec_eq_true in e2; rewrite -> e2 in *=> {e2}.
          1,2: unshelve apply: storeview_eq; [exact: is_public|..]; cook.
          unshelve apply: storeview_eq; [exact: is_trusted|..]; cook. }
          move: Hsafe=> [Hft Hpcto].
          revert_hyp_pat (if untrusted _ then _ else _); case: ifP => Hpcu.
          { (* untrusted pc: ideal_cmd is PU-well-typed; pc ⊑ to ⟹ to untrusted *)
          move=> Hic.
          have Htou : is_untrusted to := flows_from_untr _ _ Hpcu Hpcto.
          have Htf : is_trusted to = false; [rewrite /is_trusted Htou // |].
          rewrite /clean_cmd_stp_store /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
          rewrite update_storeview_nochange //.
          (* ideal_cmd preserves the trusted view (PU-well-typed), and the ideal
             corruption only touches an untrusted `from`, so both are invisible. *)
          rewrite (ni_untr_optcmd_st_int _ _ _ Hic).
          case Hg: (is_public from && is_untrusted from);
            [ move: Hg => /andP[_ Hu]; have Htf2 : is_trusted from = false;
                [ rewrite /is_trusted Hu // | rewrite update_storeview_nochange //; cook ]
            | cook ]. }
          (* trusted pc: ideal_cmd = endorse from to; both sides copy to := · from,
             so the proof reduces to the same trusted-view argument. *)
          move=> Hic; rewrite -Hic.
          rewrite /clean_cmd_stp_store /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
          apply: update_from_storeview_eq; [exact: (fun H => flows_to_tr _ _ H Hft) |].
          case Hg: (is_public from && is_untrusted from);
            [ move: Hg => /andP[_ Hu]; have Htf2 : is_trusted from = false;
                [ rewrite /is_trusted Hu // | rewrite update_storeview_nochange //; cook ]
            | cook ].
          }
        cook. revert_hyp_pat bool; case.
        1-2: revert_hyp_pat [PcLbl, (WellFormedCmd _ _), (if _ then _ else _)]; case=> [[] ?] /=.
        2,4: auto with cook_step trickbag; fail.
        1-2: revert_hyp_pat (option _); case=> /= *; cook. } 
        { let rcmd := pick_hyp_pat uconstr:(Cmd) in  move: (orbN (is_declassify rcmd))=> /orP [ | nodecl]; cycle 1.
          { revert_hyp_pat [PcLbl, (WellFormedCmd _ _), (if _ then _ else _)]; case=> [+ []] /==> *; cook. } 
        move/is_declassify_inv=> [from [to e]]; rewrite -> e in *=> {e}.
        revert_hyp_pat (WellFormedCmd _ _)=> /wf_declassify_inv [Hcanon | Hsafe].
        { move: Hcanon=> [Hpc [Hfrom Hto]]; rewrite -> Hpc in *=> {Hpc}.
        have Hg : is_secret from && is_public to; [rewrite /is_secret /is_public Hfrom Hto // |].
        rewrite Hg.
        revert_hyp_pat (if _ then _ else _)=> /= <- /=.
        apply/storeview_eq_ext=> *; rewrite /clean_assign_stp_store /update_to_store /=. rewrite dec_eq_refl. (* TODO: Eventually this should be a rewrite rule also *)
        case e1: (_ =? _).
          { unshelve apply: storeview_eq; [exact: is_trusted|..]; cook. }
        apply/storeview_eq; [|eassumption]; cook. }
        move: Hsafe=> [Hft Hpcto].
        (* Safe declassify: from ⊑ to, so a public target has a public source,
           hence the (secret-source-guarded) ideal read never fires. The copy
           to := · from then preserves the public view like an ordinary
           assignment. *)
        have Hrd : is_secret from && is_public to = false.
        { case Ht: (is_public to); [| rewrite andbF //].
          rewrite andbT /is_secret /is_public (flows_to_pub _ _ Ht Hft) //. }
        rewrite Hrd /=.
        rewrite /clean_cmd_stp_store /clean_assign_stp_store /get_assign_dest /get_assign_val /=.
        set pcl := (X in if public X then _ else _).
        case Hpcp: (public pcl).
        - apply: update_from_storeview_eq; [exact: (fun H => flows_to_pub _ _ H Hft) |].
          cook.
        - have Hts : is_public to = false.
          { rewrite /is_public; apply/negbTE; apply: (flows_from_sec pcl _ _ Hpcto).
            rewrite /secret Hpcp //. }
          rewrite update_storeview_nochange //. cook. }
      move=> /=.  
      apply/Forall_and; cook; auto.
      revert_hyp_pat [PcLbl, (WellFormedCmd _ _), (if _ then _ else _)].
      case=> [[] ?] /= >.
         { move=> *; cook.
         revert_hyp_pat [(option _), (_ ⊢ _)]; case=> //= >.
         rewrite -/(WellFormedProg _ _).
         move=> /step_soundness=> snd.
         apply/flows_to_subtype_prog;[|apply/snd]; auto. }
      move=> /= ? <- /=.
      move ?: (compute_new_pc _ _)=> [[] ?] /=; cycle 1. 
         { erewrite ni_tr_cmd_cnt; [apply/Forall_combine2_same/Forall_map/Forall_forall => // | eassumption |..]; auto with trickbag.
         let rcmd := pick_hyp_pat uconstr:(Cmd) in  move: (orbN (is_endorse rcmd))=> /orP [ | noend]; cook.
         move/is_endorse_inv=> [from [to e]]; rewrite -> e in *=> {e}.
         revert_hyp_pat (WellFormedCmd _ _)=> /wf_endorse_inv [Hcanon | Hsafe].
         { move: Hcanon=> [Hpc [Hfrom Hto]]; rewrite -> Hpc in * => {Hpc}.
         have Hg : is_public from && is_untrusted from; [rewrite /is_public /is_untrusted Hfrom // |].
         rewrite Hg /= update_storeview_nochange; cook. }
         move: Hsafe=> [Hft Hpcto].
         case Hg: (is_public from && is_untrusted from).
         { move: Hg => /andP[_ Hu].
           have Htf : is_trusted from = false; [rewrite /is_trusted Hu // |].
           rewrite update_storeview_nochange //. cook. }
         cook.
         }
      cook. rewrite-/(WellFormedProg _ _). (* TODO: lift that weakening thing to wf prog also*)
      revert_hyp_pat [Cmd, (WellFormedCmd _ _), (compute_new_pc _ _ = _)].
      move=> ? /step_soundness snd newpce.
      apply/flows_to_subtype_prog; [|apply/snd].
      auto with trickbag.
    Qed.
  End cook.

  Theorem cfg_step_inv: forall c, Invariant c ->  Invariant ((cfg_step c).1).
  Proof.
    case=> + [] //.
    rewrite/Invariant/cfg_step=> > []. Forall_inv_toph.
    rewrite [cmbcmd_step _ _]surjective_pairing.
    case e: ((cmbcmd_step _ _).1)=> h1 ? h2. 
    rewrite fst_pair. move: (cmbcmd_step_inv _ _ h1 h2).
    rewrite [cmbcmd_step _ _]surjective_pairing e=>-  [] *.
    split=> //; apply/Forall_app=> //.
  Qed.

  Print Assumptions cfg_step_inv.
End invprf.



