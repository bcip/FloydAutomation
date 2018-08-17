Require Export VST.floyd.proofauto.

(* EExists *)
Ltac my_evar name T cb :=
  let x := fresh name
  in
  evar (x : T);
    let x' := eval unfold x in x
    in
    clear x; cb x'.

Ltac tuple_evar name T cb :=
  lazymatch T with
  | prod ?A ?B => tuple_evar name A
    ltac: (fun xA =>
      tuple_evar name B ltac: (fun xB =>
        cb (xA, xB)))
  | _ => my_evar name T cb
  end; idtac.

Ltac EExists'' :=
  let EExists_core :=
    match goal with [ |- _ |-- EX x:?T, _ ] =>
      tuple_evar x T ltac: (fun x => apply exp_right with x)
    end; idtac
  in
  first [ EExists_core
         | rewrite exp_andp1; EExists''
         | rewrite exp_andp2; EExists''
         | rewrite exp_sepcon1; EExists''
         | rewrite exp_sepcon2; EExists''
         | extract_exists_from_SEP_right; EExists_core
         ].

Ltac EExists' :=
  match goal with |- ?A |-- ?B =>
     let z := fresh "z" in pose (z:=A); change (z|--B); EExists''; unfold z at 1; clear z
  end.

Ltac EExists := EExists'.

Ltac EExists_alt :=
  let T := fresh "T"
  in
  let x := fresh "x"
  in
  evar (T:Type); evar (x:T); subst T; Exists x; subst x.

(* ecancel *)
Ltac ecareful_unify :=
let is_Type_or_type T :=
  match type of T with
  | Type => idtac
  | type => idtac
  end
in
repeat match goal with
| |- ?X = ?X' => first [is_evar X | is_evar X' | constr_eq X X']; reflexivity
| |- ?F _ = ?F' _ => constr_eq F F'; apply f_equal
| |- ?F _ _ = ?F' _ _ => constr_eq F F'; apply f_equal2
| |- ?F _ _ _ = ?F' _ _ _ => constr_eq F F'; apply f_equal3
| |- ?F _ _ _ _ = ?F' _ _ _ _ => constr_eq F F'; apply f_equal4
| |- ?F _ _ _ _ _ = ?F' _ _ _ _ _ => constr_eq F F'; apply f_equal5
| |- ?F ?T = ?F' ?T' => 
    constr_eq F F'; is_Type_or_type T; change (F T = F' T)
| |- ?F ?T ?A1 = ?F' ?T' ?A1' => 
    constr_eq F F'; is_Type_or_type T; change (F T A1 = F' T A1')
| |- ?F ?T ?A1 ?A2 = ?F' ?T' ?A1' ?A2' => 
    constr_eq F F'; is_Type_or_type T; change (F T A1 A2 = F' T A1' A2')
| |- ?F ?T ?A1 ?A2 ?A3 = ?F' ?T' ?A1' ?A2' ?A3' => 
    constr_eq F F'; is_Type_or_type T; change (F T A1 A2 A3 = F' T A1' A2' A3')
| |- ?F ?T ?A1 ?A2 ?A3 ?A4 = ?F' ?T' ?A1' ?A2' ?A3' ?A4' => 
    constr_eq F F'; is_Type_or_type T; change (F T A1 A2 A3 A4 = F' T A1' A2' A3' A4')
end.

Ltac local_cancel_in_syntactic_cancel unify_tac ::=
  cbv beta;
  match goal with |- ?A |-- ?B => 
    solve [constr_eq A B; simple apply (derives_refl A) | auto with nocore cancel | apply derives_refl'; solve [unify_tac]]
  end.

Ltac syntactic_cancel unify_tac ::=
  repeat first
         [ simple apply syntactic_cancel_nil
         | simple apply syntactic_cancel_cons;
           [ find_nth ltac: (local_cancel_in_syntactic_cancel unify_tac)
           | cbv iota; unfold delete_nth; cbv zeta iota
           ]
         ].

(* To solve: Frame := ?Frame |- fold_right_sepcon G |-- fold_right_sepcon L * fold_right_sepcon Frame *)
Ltac cancel_for_evar_frame' unify_tac :=
  eapply syntactic_cancel_spec1;
  [ syntactic_cancel unify_tac
  | cbv iota; cbv zeta beta;
    first [ match goal with
            | |- _ |-- _ * fold_right_sepcon ?F => try unfold F
            end;
            simple apply syntactic_cancel_solve1
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B * _ => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].

Ltac cancel_for_evar_frame ::= cancel_for_evar_frame' careful_unify.

(* To solve: |- fold_right_sepcon G |-- fold_right_sepcon L * TT *)
Ltac cancel_for_TT unify_tac ::=
  eapply syntactic_cancel_spec1;
  [ syntactic_cancel unify_tac
  | cbv iota; cbv zeta beta;
    first [ simple apply syntactic_cancel_solve2
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B * _ => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].

Ltac cancel_for_normal unify_tac ::=
  eapply syntactic_cancel_spec3;
  [ syntactic_cancel unify_tac
  | cbv iota; cbv zeta beta;
    first [ simple apply syntactic_cancel_solve3
          | match goal with
            | |- fold_right_sepcon ?A |-- fold_right_sepcon ?B => rewrite <- (fold_left_sepconx_eq A), <- (fold_left_sepconx_eq B)
            end;
            unfold fold_left_sepconx; cbv iota beta ]
  ].

Ltac new_cancel unify_tac ::=
  match goal with
  | |- @derives mpred Nveric _ _ => idtac
  | _ => fail 1000 "Tactic cancel can only handle proof goals with form _ |-- _ (unlifted version)."
  end;
  eapply symbolic_cancel_setup;
  [ construct_fold_right_sepcon
  | construct_fold_right_sepcon
  | fold_abnormal_mpred
  | match goal with
    | |- before_symbol_cancel _ _ None =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_normal unify_tac
    | |- before_symbol_cancel _ _ (Some (fold_right_sepcon _)) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_evar_frame' unify_tac
    | |- before_symbol_cancel _ _ (Some TT) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_TT unify_tac
    | |- before_symbol_cancel _ _ (Some (prop True)) =>
           cbv iota beta delta [before_symbol_cancel];
           cancel_for_TT unify_tac
    end
  ].

Ltac cancel_unify_tac := careful_unify.
Ltac cancel ::= new_cancel cancel_unify_tac.

Lemma field_at_data_at_cancel': forall {cs : compspecs} sh t v p,
  field_at sh t nil v p = data_at sh t v p.
Proof.
  intros. apply pred_ext.
  apply field_at_data_at_cancel.
  apply data_at_field_at_cancel.
Qed.

Ltac ecancel_unify_tac :=
  rewrite ?field_at_data_at_cancel';
  rewrite ?field_at_data_at;
  rewrite ?field_at__data_at_;
  rewrite ?data_at__data_at;
  ecareful_unify.

Ltac ecancel := cancel; new_cancel ecancel_unify_tac.

(* new_sep_apply *)
Ltac sep_apply_in_entailment H :=
    match goal with |- ?A |-- ?B =>
     let H' := adjust2_sep_apply H in
     match type of H' with ?TH =>
     match apply_find_core TH with  ?C |-- ?D =>
      let frame := fresh "frame" in evar (frame: list mpred);
       apply derives_trans with (C * fold_right_sepcon frame);
             [solve [ecancel] 
             | eapply derives_trans; 
                [apply sepcon_derives; [clear frame; apply H' | apply derives_refl] 
                | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp
                ]
             ]
     end
     end
    end.


Ltac my_unshelve_evar name T cb evar_tac :=
  let x := fresh name
  in
  unshelve evar (x:T); revgoals;
  [
    let x' := eval unfold x in x
    in
    clear x; cb x'
  |
    evar_tac x
  ].

Ltac new_sep_apply_in_entailment originalH evar_tac prop_tac :=
  let rec sep_apply_in_entailment_rec H :=
    lazymatch type of H with
    | forall x:?T, _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T); revgoals; [sep_apply_in_entailment_rec (H H'); clear H' | prop_tac]; revgoals
      | _ => my_unshelve_evar x T
        ltac:(fun x => sep_apply_in_entailment_rec (H x))
        evar_tac
      end
    | ?T -> _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T); revgoals; [sep_apply_in_entailment_rec (H H'); clear H' | prop_tac]; revgoals
      | _ => let x := fresh "arg" in
        my_unshelve_evar x T
          ltac:(fun x => sep_apply_in_entailment_rec (H x))
          evar_tac
      end
    | ?A |-- ?B => sep_apply_in_entailment H
    | ?A = ?B => sep_apply_in_entailment H
    | _ => fail 0 originalH "is not an entailment"
    end
  in
  sep_apply_in_entailment_rec originalH.

Ltac new_sep_apply_in_lifted_entailment H evar_tac prop_tac :=
 apply SEP_entail;
 unfold fold_right_sepcon at 1;
 match goal with |- ?R |-- ?R2 => 
  let r2 := fresh "R2" in pose (r2 := R2); change (R |-- r2);
  new_sep_apply_in_entailment H evar_tac prop_tac;
  [ .. | match goal with |- ?R' |-- _ =>
   let R'' := refold_right_sepcon R'
     in replace R' with (fold_right_sepcon R'')
           by (unfold fold_right_sepcon; rewrite ?sepcon_emp; reflexivity);
        subst r2; apply derives_refl
   end]
 end.

Ltac new_sep_apply_in_semax H evar_tac prop_tac :=
   eapply semax_pre; [new_sep_apply_in_lifted_entailment H evar_tac prop_tac | ].

Ltac new_sep_apply H evar_tac prop_tac :=
 lazymatch goal with
 | |- ENTAIL _ , _ |-- _ => eapply ENTAIL_trans; [new_sep_apply_in_lifted_entailment H evar_tac prop_tac | ] 
 | |- @derives mpred _ _ _ => new_sep_apply_in_entailment H evar_tac prop_tac
 | |- semax _ _ _ _ => new_sep_apply_in_semax H evar_tac prop_tac
 end.

Ltac sep_apply ::=
  ltac:(fun H =>
    new_sep_apply H
      ltac:(fun x =>
        fail 0 "Unable to find an instance for the variable" x)
      ltac:(first [assumption | reflexivity | idtac])).

Ltac new_sep_eapply_in_entailment originalH :=
  let rec sep_eapply_in_entailment_rec H :=
    lazymatch type of H with
    | forall x:?T, _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T); [try reflexivity | sep_eapply_in_entailment_rec (H H'); clear H']
      | _ => my_evar x T ltac:(fun x => sep_eapply_in_entailment_rec (H x))
      end
    | ?T -> _ =>
      lazymatch type of T with
      | Prop => let H' := fresh "H" in assert (H':T); [try reflexivity | sep_eapply_in_entailment_rec (H H'); clear H']
      | _ => let x := fresh "arg" in my_evar x T ltac:(fun x => sep_eapply_in_entailment_rec (H x))
      end
    | ?A |-- ?B => sep_apply_in_entailment H
    | ?A = ?B => sep_apply_in_entailment H
    | _ => fail 0 originalH "is not an entailment"
    end
  in
  sep_eapply_in_entailment_rec originalH.

Ltac new_sep_eapply_in_lifted_entailment H :=
 apply SEP_entail;
 unfold fold_right_sepcon at 1;
 match goal with |- ?R |-- ?R2 => 
  let r2 := fresh "R2" in pose (r2 := R2); change (R |-- r2);
  new_sep_eapply_in_entailment H;
  [ .. | match goal with |- ?R' |-- _ =>
   let R'' := refold_right_sepcon R' 
     in replace R' with (fold_right_sepcon R'') 
           by (unfold fold_right_sepcon; rewrite ?sepcon_emp; reflexivity);
        subst r2; apply derives_refl
   end]
 end.

Ltac new_sep_eapply_in_semax H :=
   eapply semax_pre; [new_sep_eapply_in_lifted_entailment H | ].

Ltac new_sep_eapply H :=
 lazymatch goal with
 | |- ENTAIL _ , _ |-- _ => eapply ENTAIL_trans; [new_sep_eapply_in_lifted_entailment H | ] 
 | |- @derives mpred _ _ _ => new_sep_eapply_in_entailment H
 | |- semax _ _ _ _ => new_sep_eapply_in_semax H
 end.

Ltac sep_eapply :=
  ltac:(fun H =>
    new_sep_apply H
      ltac:(fun _ => shelve)
      ltac:(first [assumption | reflexivity | idtac])).

Lemma allp_instantiate': forall {B} (P : B -> mpred) x,
  allp P |-- P x.
Proof. intros. apply allp_instantiate. Qed.
