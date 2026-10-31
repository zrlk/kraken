import WeakCore.TermPredRdM
import WeakCore.TermPromStep
import WeakCore.TermPredStoreFree

/-! # TermPredRd: `PredRdF`

A read raising the stepper's coherence at a predicted unit `b` (`PredU`) of its own buffer, off the
two-word units of the cell, to an old non-promise message `K′` does not land on a placeholder.

The read goes through a reference to a component containing `b` (`Foot`): an `own` reference's
slot is below the real count (`IniAt` at `modeIni .own = rc`), which makes `b` initialised at the
real count (`IniWr`), against `PredU`; a `pub` reference carries the frontier `f ≤ pw.view`
(`ModeOK`, the cell unseen by `OwnHidP` part 2), and the read's message has no later message at `b`
up to `pw.view` (`TermPredRdM.tstep_rdv`), so by `HiddenP` below `f` it is a typed word, while
`undef` is no word at the `.one` unit containing `b` (`noTwo_oneAt`, `undef_nwordOK_one`).
-/

namespace TermPredRd

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermB5 TermForWU TermFul
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermReadClsM TermReadCls TermPredRdM

/-! ## Layout: off the two-word units, a `.one` unit -/

theorem oneAt_of_noTwo : ∀ (us : List Acc) (k : Nat), k < nWords us →
    (∀ q, TwoAt us q → k ≠ q ∧ k ≠ q + 1) → TermFul.OneAt us k
  | [], k, h, _ => by simp [nWords] at h
  | .one :: us, 0, _, _ => .here us
  | .one :: us, k + 1, h, hn => by
      have hk : k < nWords us := by simp [nWords, Acc.size] at h ⊢; omega
      have ih := oneAt_of_noTwo us k hk fun q hq => by
        have := hn (q + 1) (by simpa [Acc.size] using TermStep.TwoAt_cons Acc.one hq)
        omega
      simpa [Acc.size] using TermFul.OneAt.cons Acc.one ih
  | .two :: us, 0, _, hn => absurd rfl (hn 0 ⟨0, rfl, rfl⟩).1
  | .two :: us, 1, _, hn => absurd rfl (hn 0 ⟨0, rfl, rfl⟩).2
  | .two :: us, k + 2, h, hn => by
      have hk : k < nWords us := by simp [nWords, Acc.size] at h ⊢; omega
      have ih := oneAt_of_noTwo us k hk fun q hq => by
        have := hn (q + 2) (by simpa [Acc.size] using TermStep.TwoAt_cons Acc.two hq)
        omega
      simpa [Acc.size] using TermFul.OneAt.cons Acc.two ih

#print axioms oneAt_of_noTwo

/-- In a buffer cell, a word of a component off the cell's two-word units is in a `.one` unit. -/
theorem noTwo_oneAt {T U e : Ty} {N ao bo : Nat} {us : List Acc} (hT : T = .array (.lit N) e)
    (hat : AtOff T ao U) (hus : accs U = some us) (hle : ao ≤ bo) (hlt : bo < ao + nWords us)
    (hno : ∀ q, TwoAtT T q → bo ≠ q ∧ bo ≠ q + 1) : TermFul.OneAt us (bo - ao) := by
  rcases AtOff_arr_elem hat hT with hU | ⟨ue, j2, o', hue, hj2, ho, hat'⟩
  · rw [hU, hT] at hus; simp [accs] at hus
  obtain ⟨pre, post, hL, hn⟩ := AtOff_embed hat' hue hus
  refine oneAt_of_noTwo us (bo - ao) (by omega) fun q hq => ?_
  have h2 : TwoAt ue (nWords pre + q) := by rw [hL]; exact TwoAt_embed hq
  have h3 : TwoAtT T (ao + q) :=
    ⟨j2 * nWords ue, e, ue, nWords pre + q, Or.inr ⟨N, ue, j2, hT, hue, hj2, rfl⟩, hue, h2, by omega⟩
  have := hno _ h3
  omega

#print axioms noTwo_oneAt

/-! ## The foot of a read -/

/-- `b` lies in a component at `a` reached through a reference word `pw` of mode `own`, or `pub`
with no message at `b` in `(K, pw.view]`. -/
def Foot (η : TEnv) (mem : Memory) (K : Ts) (b : Address) (pw : Word) : Prop :=
  ∃ (a : Address) (c : Cell) (U : Ty) (us : List Acc) (μ : Mode), η.sto a.label = some c ∧
    a.label = b.label ∧ AtOff c.ty a.offset U ∧ accs U = some us ∧ a.offset ≤ b.offset ∧
    b.offset < a.offset + nWords us ∧ (μ = .own ∨ (μ = .pub ∧ RdV mem b K pw.view)) ∧
    ModeOK η.tid η.pfr η.seen μ a.label c [pw] ∧ IniAt (modeIni μ η.ini η.rini) c a U

theorem foot_mk {η : TEnv} {mem : Memory} {K : Ts} {b : Address} {pw : Word} {a : Address} {c : Cell}
    {U : Ty} {us : List Acc} {μ : Mode} {j : Nat} (hsto : η.sto a.label = some c)
    (hat : AtOff c.ty a.offset U) (hus : accs U = some us) (hj : j < nWords us) (hb : b = offs a (0 + j))
    (hμ : μ = .own ∨ (μ = .pub ∧ RdV mem b K pw.view))
    (hmo : ModeOK η.tid η.pfr η.seen μ a.label c [pw]) (hini : IniAt (modeIni μ η.ini η.rini) c a U) :
    Foot η mem K b pw := by
  subst hb
  have e : (offs a (0 + j)).offset = a.offset + j := by simp [offs]
  refine ⟨a, c, U, us, μ, hsto, rfl, hat, hus, ?_, ?_, hμ, hmo, hini⟩
  · rw [e]; exact Nat.le_add_right _ _
  · rw [e]; exact Nat.add_lt_add_left hj _

/-- **No placeholder under a foot.** -/
theorem foot_false {g : G} {η : TEnv} {s : St} {b : Address} {cl : Cell} {pw : Word} {K : Ts} {m : Msg}
    (hm : MemInv g (CE η) s) (hsto : (CE η).sto b.label = some cl) (ho : cl.owner = some η.tid)
    (hq : PredU (CE η) b) (hno : ∀ q, TwoAtT cl.ty q → b.offset ≠ q ∧ b.offset ≠ q + 1)
    (hf : Foot η s.mem K b pw) (hK : K ∉ s.promises) (hmK : s.mem[K]? = some m) (hund : m.val = .undef) :
    False := by
  obtain ⟨N, e, ue, hT, hue⟩ : ∃ N e ue, cl.ty = .array (.lit N) e ∧ accs e = some ue :=
    (Classical.em _).elim id fun hn => False.elim <| hq.2.2 fun c' N' e' us' h1 h2 h3 => by
      rw [hsto] at h1; cases h1; exact absurd ⟨N', e', us', h2, h3⟩ hn
  obtain ⟨a, c, U, us, μ, hsa, hla, hat, hus, hle, hlt, hμ, hmo, hini⟩ := hf
  have hsa' : (CE η).sto b.label = some c := by rw [← hla]; exact hsa
  rw [hsto] at hsa'
  cases hsa'
  rcases hini N e hT with ⟨hU, -⟩ | ⟨ue', j, o, hue', hj, hjo, hat'⟩
  · rw [hU, hT] at hus; simp [accs] at hus
  rw [hue] at hue'
  cases hue'
  have hb1 : o + nWords us ≤ nWords ue := AtOff_bound hat' hue hus
  obtain ⟨ao, hao⟩ : ∃ x : Nat, a.offset = x := ⟨_, rfl⟩
  obtain ⟨bo, hbo⟩ : ∃ x : Nat, b.offset = x := ⟨_, rfl⟩
  rcases hμ with rfl | ⟨rfl, hrd⟩
  · apply hq.2.2
    intro c' N' e' us' h1 h2 h3
    rw [hsto] at h1; cases h1; rw [hT] at h2; cases h2; rw [hue] at h3; cases h3
    have hjr : j < (CE η).rc b.label := by
      have : j < modeIni .own η.ini η.rini a.label := hj
      rw [hla] at this; exact this
    have hm2 : (j + 1) * nWords ue ≤ (CE η).rc b.label * nWords ue := Nat.mul_le_mul_right _ hjr
    rw [Nat.succ_mul] at hm2
    have hlt2 : bo < ao + nWords us := by rw [← hao, ← hbo]; exact hlt
    have hjo2 : j * nWords ue + o = ao := by rw [← hao]; exact hjo
    rw [hbo]
    calc bo < ao + nWords us := hlt2
      _ = j * nWords ue + (o + nWords us) := by rw [← hjo2, Nat.add_assoc]
      _ ≤ j * nWords ue + nWords ue := Nat.add_le_add_left hb1 _
      _ ≤ (CE η).rc b.label * nWords ue := hm2
  · obtain ⟨f, hf, hfv⟩ := hmo
    have hIni : bo < (CE η).ini b.label * nWords ue := hbo ▸ hq.2.1 cl N e ue hsto hT hue
    have hrc : (CE η).rc b.label < (CE η).ini b.label := by
      refine Nat.lt_of_not_le fun hle2 => hq.2.2 fun c' N' e' us' hc' hT' hus' => ?_
      rw [hsto] at hc'; cases hc'; rw [hT] at hT'; cases hT'; rw [hue] at hus'; cases hus'
      rw [hbo]
      exact Nat.lt_of_lt_of_le hIni (Nat.mul_le_mul_right _ hle2)
    obtain ⟨f', hf', hns, hH⟩ := hm.2.2.2.2.2.1.2 b.label cl hsto ho hrc
    have hf2 : (CE η).pfr b.label = some f := by rw [← hla]; exact hf
    have ef : f = f' := by rw [hf'] at hf2; exact (Option.some.inj hf2).symm
    subst ef
    have hfv' : f ≤ pw.view := by
      rcases hfv with hs | hv
      · exact absurd (show (CE η).seen b.label by rw [← hla]; exact hs)
          (hns (ZW.not_of_initR hsto fun N' e' us' h2 h3 => hq.2.1 cl N' e' us' hsto h2 h3))
      · exact hv pw (List.mem_singleton_self _)
    have hInit : InitR (CE η) cl b.label b.offset := fun N' e' us' h2 h3 => hq.2.1 cl N' e' us' hsto h2 h3
    obtain ⟨⟨m', hm', hl'⟩, hrd2⟩ := hrd
    rw [hmK] at hm'
    cases hm'
    have hone := noTwo_oneAt hT hat hus hle hlt hno
    have hnw : ¬ WordOK (CE η) cl.ty b.offset (mw m) := by
      have := TermPromStep.undef_nwordOK_one (E := CE η) (w := mw m) hat hus hone hund
      rwa [Nat.add_sub_cancel' hle] at this
    have hbe : b = ⟨b.label, b.offset⟩ := rfl
    obtain ⟨t', m'', hlt', hle', hm'', hl''⟩ := hH b.offset hInit K m hK hmK (hl'.trans hbe) hnw
    exact hrd2 t' m'' hlt' (Nat.le_trans hle' hfv') hm'' (hl''.trans hbe.symm)

#print axioms foot_false

/-! ## Feet of the reads -/

theorem cell_eq {t u u' : Ty} {μ μ' : Mode} (h1 : t = .ptr μ u ∨ t = .loc μ u)
    (h2 : t = .ptr μ' u' ∨ t = .loc μ' u') : μ = μ' ∧ u = u' := by
  rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> cases h <;> exact ⟨rfl, rfl⟩

/-- A reference read's foot. -/
theorem foot_ptr {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty} {μ : Mode}
    {u rt : Ty} {pw : Word} {b0 b : Address} {us : List Acc} {j : Nat} {mem : Memory} {K : Ts}
    (hvars : VarsOK ρ η σs cx.vars env) (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hμ : μ = .own ∨ μ = .pub) (hea : evalAt env a = some (rt, [pw])) (hb0 : addrOf pw = some b0)
    (hus : accs (cl ρ η.wit 0 0 u) = some us) (hj : j < nWords us) (hb : b = offs b0 (0 + j))
    (hrd : RdV mem b K pw.view) : Foot η mem K b pw := by
  obtain ⟨c, U, hsto, hat, hFd, hmo, hini⟩ := TermPredStoreFree.ptr_targetM hvars hp ht hea hb0
  refine foot_mk hsto hat ((Fd_accs hFd).trans hus) hj hb ?_ hmo hini
  rcases hμ with rfl | rfl
  · exact .inl rfl
  · exact .inr ⟨rfl, hrd⟩

theorem accs_word {ρ : Nat → Nat} {W : Nat → Ty} {r : Idx} {P : Proto} (hg : P.ghost = false) :
    accs (cl ρ W 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]

theorem accs_int {ρ : Nat → Nat} {W : Nat → Ty} : accs (cl ρ W 0 0 .int) = some [.one] := by simp [cl, accs]

theorem accs_pair {ρ : Nat → Nat} {W : Nat → Ty} {u : Ty}
    (h : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P)) : accs (cl ρ W 0 0 u) = some [.two] := by
  rcases h with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [cl, accs]

theorem offs_pair {b0 b : Address} (hb : b = b0 ∨ b = b0.next) : ∃ j, j < nWords [Acc.two] ∧ b = offs b0 (0 + j) := by
  rcases hb with rfl | rfl
  · exact ⟨0, by simp [nWords, Acc.size], by cases b; simp [offs]⟩
  · exact ⟨1, by simp [nWords, Acc.size], by cases b0; simp [offs, WeakMem.Address.next]⟩

theorem one_lt : 0 < nWords [Acc.one] := by simp [nWords, Acc.size]

/-- Loads. -/
theorem load_foot {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {acq : Bool} {a : At} {b : Address} {mem : Memory} {Kt : Ts}
    (hop : OpT p cx x (.load acq a) c') (hsc : OpScope cx (.load acq a))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hrd : RdOp g env s (.load acq a) b)
    (hR : ∀ t pw, evalAt env a = some (t, [pw]) → RdV mem b Kt pw.view) : ∃ pw, Foot η mem Kt b pw := by
  obtain ⟨rt, pw, μr, ru, b0, us, j, hea, hcr, hb0, hus, hj, hb⟩ := hrd
  have go : ∀ {t u : Ty} {μ : Mode}, cx.peek a = .ok t → cellOf t = some (μ, u) → (μ = .own ∨ μ = .pub) →
      cx.opaqueOK u = true → ∃ pw, Foot η mem Kt b pw := by
    intro t u μ hp hc hμ hop
    have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
      (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc hop hea hcr).symm.trans hus
    exact ⟨pw, foot_ptr hi.2.1 hp (cell_cases hc) hμ hea hb0 hacc hj hb (hR _ _ hea)⟩
  cases hop with
  | loadOwn hp _ hc _ hbind => exact go hp hc (.inl rfl) (bind_opaqueOK hbind)
  | loadPub hp _ hc _ _ hbind => exact go hp hc (.inr rfl) (bind_opaqueOK hbind)
  | loadRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | loadCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | loadTorn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | @loadWord _ _ _ _ tw rP hp hw hg _ =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      have hc : cellOf tw = some (μ, Ty.word rP.1 rP.2) := by rcases ht with rfl | rfl <;> rfl
      have hμ : μ = .own ∨ μ = .pub := by
        cases μ with
        | own => exact .inl rfl
        | pub => exact .inr rfl
        | rgn r => exact absurd hc (hsc _ hp _ _)
      exact go hp hc hμ (by simp [Cx.opaqueOK, Ty.guardT])

#print axioms load_foot

/-- Own-buffer slot loads. -/
theorem loadAt_foot {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb i : At} {b : Address} {mem : Memory} {Kt : Ts}
    (hop : OpT p cx x (.loadAt bb i) c') (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hrd : RdOp g env s (.loadAt bb i) b) : ∃ pw, Foot η mem Kt b pw := by
  obtain ⟨rt, pw, ti, iws, μ, u0, j0, a0, us, j, hea, hei, hbe, hnj, hb, hus, hj, hbb⟩ := hrd
  cases hop with
  | loadAt hp hbuf hint hlt hltk haf hbind =>
      have ho := bind_opaqueOK hbind
      obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, hini,
        -, -, htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      exact ⟨pw, foot_mk (a := offs a0 _) hsto hat ((buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus) hj hbb (.inl rfl)
        hmo hini⟩

#print axioms loadAt_foot

theorem loadAtF_foot {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb i : At} {q : List Nat} {b : Address} {mem : Memory}
    {Kt : Ts}
    (hop : OpT p cx x (.loadAtF bb i q) c') (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hrd : RdOp g env s (.loadAtF bb i q) b) : ∃ pw, Foot η mem Kt b pw := by
  obtain ⟨rt, pw, ti, iws, μ, u0, j0, a0, us0, c0, o0, cs, j, hea, hei, hbe, hnj, hb, hus0, hco0, hcs, hj, hbb⟩ :=
    hrd
  cases hop with
  | loadAtF hp hbuf hct hopu hint hlt hltk haf hbind =>
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, hmo, -,
        hsku, hsig, htbu, hall⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hnj] at hnj'
      simp only [Option.some.injEq] at hnj'
      subst hnj'
      rw [hus0] at hus'
      simp only [Option.some.injEq] at hus'
      subst hus'
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
      rw [hco0] at hco
      simp only [Option.some.injEq, Prod.mk.injEq] at hco
      obtain ⟨rfl, rfl⟩ := hco
      have htbc := TermStep.tb_compTy q _ _ hct htbu
      have ho := bind_opaqueOK hbind
      have hacc : accs (cl ρ η.wit 0 0 _) = some cs :=
        (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htbc hi.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
            hco0)).symm.trans hcs)
      refine ⟨pw, foot_mk (a := offs a0 (ev ρ _ * nWords us0 + o0)) hsto ?_ hacc hj hbb (.inl rfl) hmo
        (hall _ _ hato)⟩
      simpa [offs, Nat.add_assoc] using AtOff_trans hat hato

#print axioms loadAtF_foot

theorem ldl_foot {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb i : At} {b : Address} {mem : Memory} {Kt : Ts}
    (hop : OpT p cx x (.ldl bb i) c') (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hrd : RdOp g env s (.ldl bb i) b) : ∃ pw, Foot η mem Kt b pw := by
  obtain ⟨rt, pw, t1, iws, μ0, u0, j0, a0, sg0, w0, jx, hea, hei, hbe, hnj, hb, hlo0, hjx, hbb⟩ := hrd
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk _ =>
      obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jj q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i jj ∧
          LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k) :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu hlt hltk
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_num hi.2.1 hpi hti
      have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
      have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
      have hJ : ev ρ jj / w.lanes < ev ρ n :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
      have hJk : ev ρ jj / w.lanes < ev ρ k :=
        (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
      obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, hmo, hini, hsku, -⟩ :=
        slot_viewN (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨pw, foot_mk (a := offs a0 _) hsto hat (by simp [cl, accs]) hjx hbb (.inl rfl) hmo hini⟩

#print axioms ldl_foot

theorem ldlw_foot {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {s : St} {x : String} {bb wi jl : At} {b : Address} {mem : Memory} {Kt : Ts}
    (hop : OpT p cx x (.ldlw bb wi jl) c') (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hrd : RdOp g env s (.ldlw bb wi jl) b) : ∃ pw, Foot η mem Kt b pw := by
  obtain ⟨rt, pw, t1, iws, t2, jws, μ0, u0, i0, j0, a0, sg0, w0, jx, hea, hei, -, hbe, hni, -, hb, hlo0, hjx,
    hbb⟩ := hrd
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ : ∃ t u n k jw q,
          cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
          LtI cx jw n ∧ LtI cx jw k :=
        ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩
      obtain ⟨sg, w⟩ := q
      have hu := lanes_of hlo
      simp only at hu
      subst hu
      have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
      obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, hmo, hini,
        hsku, -, -, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      rw [hni] at hni'
      simp only [Option.some.injEq] at hni'
      subst hni'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
      obtain ⟨rfl, rfl⟩ := hlo0
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
      rw [e1] at hat hini
      exact ⟨pw, foot_mk (a := offs a0 _) hsto hat (by simp [cl, accs]) hjx hbb (.inl rfl) hmo hini⟩

#print axioms ldlw_foot

/-- Fetches. -/
theorem fetch_foot {p : Prog} {g : G} {mem0 : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {t : Ty} {pw : Word}
    {b : Address} {mem : Memory} {Kt : Ts}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem0 pairs th)) (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some b)
    (hrd : RdV mem b Kt pw.view) : Foot η mem Kt b pw := by
  have hb' : b = offs b (0 + 0) := (TermReadCls.offs_zero b).symm
  cases hop with
  | @fetchCell _ _ _ _ _ _ _ _ tw _ hp _ hc =>
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      obtain ⟨μ, hc0⟩ : ∃ μ, cellOf tw = some (μ, Ty.int) := by
        rcases hc with hc0 | ⟨r, hc0, -⟩
        · exact ⟨_, hc0⟩
        · exact ⟨_, hc0⟩
      obtain ⟨-, rfl⟩ := cell_eq (cell_cases hc0) ht'
      exact foot_ptr hi.2.1 hp ht' hμ' hea hb accs_int one_lt hb' hrd
  | fetchEpoch hp hw hep =>
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      have hμ := word_mode ht ht' hμ'
      have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
      obtain ⟨-, rfl⟩ := cell_eq ht ht'
      exact foot_ptr hi.2.1 hp ht' hμ' hea hb (accs_word hg) one_lt hb' hrd
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨-, rfl⟩ := cell_eq ht ht'
      exact foot_ptr hi.2.1 hp ht' hμ' hea hb (accs_word hok.1.1.1.1) one_lt hb' hrd

#print axioms fetch_foot

/-- `cas`. -/
theorem cas_foot {p : Prog} {g : G} {mem0 : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop}
    {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String} {ok fail : Expr} {t : Ty} {pw : Word}
    {b : Address} {mem : Memory} {Kt : Ts}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem0 pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some b)
    (hrd : RdV mem b Kt pw.view) : Foot η mem Kt b pw := by
  have hb' : b = offs b (0 + 0) := (TermReadCls.offs_zero b).symm
  have sc : ∀ {tw}, cx.peek w = .ok tw → ∃ μ' u', (tw = .ptr μ' u' ∨ tw = .loc μ' u') ∧ (μ' = .own ∨ μ' = .pub) := by
    intro tw hp
    rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, ht', -⟩
    · exact ⟨μ', _, ht', hμ'⟩
    · exact ⟨.pub, u, ht', .inr rfl⟩
  have word : ∀ {tw r P}, cx.peek w = .ok tw → wordOf tw = some (r, P) → P.ghost = false →
      Foot η mem Kt b pw := by
    intro tw r P hp hw hg
    obtain ⟨μ', u', ht', hμ'⟩ := sc hp
    obtain ⟨μ, ht⟩ := wordOf_cases hw
    obtain ⟨-, rfl⟩ := cell_eq ht ht'
    exact foot_ptr hi.2.1 hp ht' hμ' hea hb (accs_word hg) one_lt hb' hrd
  cases hT with
  | @casCell _ _ _ _ _ _ _ _ _ _ _ tw u _ _ hp _ hc hraw _ =>
      obtain ⟨μ', u', ht', hμ'⟩ := sc hp
      obtain ⟨μ, hc0⟩ : ∃ μ, cellOf tw = some (μ, u) := by
        rcases hc with hc0 | ⟨r, hc0, -⟩
        · exact ⟨_, hc0⟩
        · exact ⟨_, hc0⟩
      obtain ⟨-, rfl⟩ := cell_eq (cell_cases hc0) ht'
      exact foot_ptr hi.2.1 hp ht' hμ' hea hb (accs_cl_one hraw) one_lt hb' hrd
  | casShare hp hw hg => exact word hp hw hg
  | casTake hp hw hg => exact word hp hw hg
  | casEpoch hp hw hep =>
      obtain ⟨μ', u', ht', hμ'⟩ := sc hp
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      have hμ := word_mode ht ht' hμ'
      exact word hp hw (pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep)

#print axioms cas_foot

/-! ## The step -/

theorem op_foot {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {op : Op} {e : Expr} {b : Address} {Kt : Ts}
    (hop : OpT p cx x op c') (hsc : OpScope cx op ∨ OpScopeR th.σs cx op)
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hrd : RdOp g th.env (stOf mem pairs th) op b)
    (hR : ∀ a t pw, PtrTerm (.let_ x op e) a → evalAt th.env a = some (t, [pw]) → RdV mem b Kt pw.view) :
    (∃ pw, Foot η mem Kt b pw) ∨ (CE η).sto b.label = none := by
  cases op
  case load acq a =>
    rcases hsc with h | h
    · exact .inl (load_foot hop h hi hE htv hrd fun t pw hea => hR a t pw (.inl ⟨x, acq, e, rfl⟩) hea)
    · simp only [OpScopeR] at h
  case ldp acq a n0 n1 =>
    obtain ⟨rt, pw, b0, j, hea, -, hb0, hj, hb⟩ := hrd
    rcases hsc with h | h
    · cases hop with
      | ldp hp _ _ =>
          obtain ⟨μ, u, ht, hμ, hu⟩ := h _ hp
          exact .inl ⟨pw, foot_ptr hi.2.1 hp ht hμ hea hb0 (accs_pair hu) hj hb
            (hR _ _ _ (.inr (.inl ⟨x, acq, n0, n1, e, rfl⟩)) hea)⟩
    · simp only [OpScopeR] at h
  case fetch o acq rel a v =>
    obtain ⟨rt, pw, tv, nw, hea, -, hb⟩ := hrd
    rcases hsc with h | h
    · exact .inl ⟨pw, fetch_foot hop h hi hE htv hm hea hb (hR _ _ _ (.inr (.inr (.inl ⟨x, o, acq, rel, v, e, rfl⟩))) hea)⟩
    · simp only [OpScopeR] at h
  case loadAt bb i => exact .inl (loadAt_foot hop hi hE htv hrd)
  case loadAtF bb i q => exact .inl (loadAtF_foot hop hi hE htv hrd)
  case ldl bb i => exact .inl (ldl_foot hop hi htv hrd)
  case ldlw bb wi jl => exact .inl (ldlw_foot hop hi htv hrd)
  case inl τ a =>
    cases hop with
    | inl _ hu _ => exact .inr (box_none hE hi htv hm hu hrd)
  case inr τ a =>
    cases hop with
    | inr _ hu _ => exact .inr (box_none hE hi htv hm hu hrd)
  case new a _ =>
    refine .inr ?_
    have hf : b.label = _ := hrd
    rw [hf]; exact (hm.2.2.2.1.1 _ (Nat.le_refl _)).1
  case newBuf n τ =>
    refine .inr ?_
    have hf : b.label = _ := hrd
    rw [hf]; exact (hm.2.2.2.1.1 _ (Nat.le_refl _)).1
  all_goals simp only [RdOp] at hrd

#print axioms op_foot

/-- **PredRd, step form.** -/
theorem tstep_predRd {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {r : Memory × List Ts × TTh} {b : Address} {cl : Cell}
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx) (hi : FInv ρ η th.σs K cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (h : r ∈ tstep g mem pairs th)
    (hsto : (CE η).sto b.label = some cl) (ho : cl.owner = some η.tid) (hq : PredU (CE η) b)
    (hno : ∀ q, TwoAtT cl.ty q → b.offset ≠ q ∧ b.offset ≠ q + 1)
    (h1 : th.vs.coh b < r.2.2.vs.coh b) (h2 : r.2.2.vs.coh b < mem.size) (h3 : r.2.2.vs.coh b ∉ th.promises) :
    ∀ m, mem[r.2.2.vs.coh b]? = some m → m.val ≠ .undef := by
  intro m hmK hund
  have fin : ∀ pw, Foot η mem (r.2.2.vs.coh b) b pw → False := fun pw hf =>
    foot_false (s := stOf mem pairs th) hm hsto ho hq hno hf h3 hmK hund
  have nn : (CE η).sto b.label ≠ none := by rw [hsto]; exact Option.some_ne_none _
  have hR : ∀ a t pw, PtrTerm th.term a → evalAt th.env a = some (t, [pw]) →
      RdV mem b (r.2.2.vs.coh b) pw.view := fun a t pw hpt hea => tstep_rdv h hpt hea h1 h2 h3
  rcases tstep_rd h (MemInv_promLt hm) h1 h2 h3 with ⟨x, op, e, hterm, hrd⟩ | ⟨a, x, e1, y, e2, hterm, hB⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t, pw, hterm, hea, hb⟩ |
      ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, t, pw, b0, hterm, hea, hb0, hb⟩
  · have hR' := hR
    rw [hterm] at hT hsc hR'
    cases hT with
    | let_ hop _ =>
        rcases op_foot hop hsc hi hE htv hm hrd hR' with ⟨pw, hf⟩ | hn
        · exact fin pw hf
        · exact nn hn
  · rw [hterm] at hT
    cases hT with
    | case hu _ _ _ _ => exact nn (box_none hE hi htv hm hu hB)
  · have hrd := hR w t pw (by rw [hterm]; exact .inr (.inr (.inr (.inl ⟨acq, rel, e, v, tn, ok, fail, rfl⟩)))) hea
    rw [hterm] at hT hsc
    rcases hsc with hs | hs
    · exact fin pw (cas_foot hT hs hi hE htv hm hea hb hrd)
    · simp only [StepScopeR] at hs
  · have hrd := hR w t pw (by rw [hterm]; exact .inr (.inr (.inr (.inr
      ⟨acq, rel, e0, e1, v0, v1, tn, ok, fail, rfl⟩)))) hea
    rw [hterm] at hT hsc
    obtain ⟨tw, hp⟩ : ∃ tw, cx.peek w = .ok tw := by cases hT <;> exact ⟨_, by assumption⟩
    rcases hsc with hs | hs
    · obtain ⟨μ, u, ht, hμ, hu⟩ := hs _ hp
      obtain ⟨j, hj, hbj⟩ := offs_pair hb
      exact fin pw (foot_ptr hi.2.1 hp ht hμ hea hb0 (accs_pair hu) hj hbj hrd)
    · simp only [StepScopeR] at hs

#print axioms tstep_predRd

theorem PredU_congr {E E' : TEnv} {a : Address} (hs : ∀ l, E'.sto l = E.sto l) (hp : E'.pfr = E.pfr)
    (hi : E'.ini = E.ini) (hr : E'.rini = E.rini) (h : PredU E a) : PredU E' a := by
  have hs' : E'.sto = E.sto := funext hs
  have hrc : E'.rc = E.rc := by funext l; unfold TEnv.rc; rw [hi, hr]
  unfold PredU IniW IniWr at *
  rw [hs', hp, hi, hrc]
  exact h

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `PredRdF` as stated (`TermOwnCRead.PredRdF`, with the two-word exclusion). -/
def PredRdFE (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ (b : Address) (cl : Cell), (CE η).sto b.label = some cl → cl.owner = some i → PredU (CE η) b →
      (∀ q, TwoAtT cl.ty q → b.offset ≠ q ∧ b.offset ≠ q + 1) →
      th.vs.coh b < r.2.2.vs.coh b → r.2.2.vs.coh b < c.mem.size → r.2.2.vs.coh b ∉ th.promises →
      ∀ m, c.mem[r.2.2.vs.coh b]? = some m → m.val ≠ .undef

/-- **`PredRdFE` holds** (from the scope obligation). -/
theorem tctx_predRd (hsc : StepScopeF p k arch Sp Init MintOK c0) : PredRdFE p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y _ b cl hsto ho hq hno h1 h2 h3
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hE2, hT2, htv2, hi2, hsum2⟩ := hRE0
  have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
    ⟨hce2, congrArg (fun E => E.tid) hce2, hE2, hT2, htv2, hi2, hsum2.1⟩
  have hs0 := hsc X Y2
  have hm : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
  have hFi : FInv ρ2 η2 th.σs (Resume p th.stack) cx2 th.env :=
    FInvR_FInv (htv2.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs2 E rd ws R h) hi2
  have hst : ∀ l, (CE η2).sto l = (CE η).sto l := fun l => by rw [Y.1, hce2]; rfl
  have ho2 : cl.owner = some η2.tid := by rw [Y2.2.1]; exact ho
  have hq2 : PredU (CE η2) b :=
    PredU_congr hst (by rw [Y.1, hce2]; rfl) (by rw [Y.1, hce2]; rfl) (by rw [Y.1, hce2]; rfl) hq
  exact tstep_predRd hE2 hT2.1 htv2 hFi hm hs0 X.hr (by rw [hst]; exact hsto) ho2 hq2 hno h1 h2 h3

#print axioms tctx_predRd

end

end TermPredRd
