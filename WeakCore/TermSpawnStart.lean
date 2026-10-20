import WeakCore.TermSpawnF0
import WeakCore.TermSpawnRun
/-!
# TermSpawnStart — the clean start (J-a) and the run lift to the phantom setup end

At an `InitOK` configuration no label has a frontier (`pfr = none`), so a live thread's cut sees
only its own cells.  Restricting `E_g`'s store to cells with a live (or no) owner changes no live
thread's cut, keeps every `SysInvW` clause, and gives `OwnLive`; the observer clauses are vacuous
(no frontier).  Hence `SysInvO` at the start, and along the phantom setup run.
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermSpawnSim
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- An owner is live among `n` threads (or there is none). -/
def liveB (n : Nat) : Option Nat → Bool
  | some i => decide (i < n)
  | none => true

/-- `E_g` with only the cells of live (or no) owners. -/
def EgR (n : Nat) (Eg : GEnv) : GEnv := { Eg with sto := fun l => (Eg.sto l).filter (fun cl => liveB n cl.owner) }

theorem sto_R {n : Nat} {Eg : GEnv} {l : AllocLabel} {cl : Cell} :
    (EgR n Eg).sto l = some cl ↔ Eg.sto l = some cl ∧ liveB n cl.owner = true := by
  show (Eg.sto l).filter (fun cl => liveB n cl.owner) = some cl ↔ _
  cases Eg.sto l with
  | none => simp
  | some c =>
    cases h : liveB n c.owner
    · simp only [Option.filter, h]
      exact ⟨fun e => (by cases e), fun ⟨e, e2⟩ => by cases e; rw [h] at e2; cases e2⟩
    · simp only [Option.filter, h]
      exact ⟨fun e => (by cases e; exact ⟨rfl, h⟩), fun ⟨e, _⟩ => e⟩

theorem sto_R_none {n : Nat} {Eg : GEnv} {l : AllocLabel} (h : Eg.sto l = none) : (EgR n Eg).sto l = none := by
  show (Eg.sto l).filter _ = none
  rw [h]; rfl

theorem sto_R_sub {n : Nat} {Eg : GEnv} {l : AllocLabel} {cl : Cell} (h : (EgR n Eg).sto l = some cl) :
    Eg.sto l = some cl := (sto_R.1 h).1

theorem cutSto_R {n i : Nat} {Eg : GEnv} (hi : i < n) (hpf : ∀ l, Eg.pfr l = none) :
    cutSto (EgR n Eg) i = cutSto Eg i := by
  funext l
  have nsh : ∀ (E : GEnv), E.pfr = Eg.pfr → ¬ E.Shared l := fun E e ⟨f, hf⟩ => by
    rw [e, hpf l] at hf; cases hf
  cases e1 : cutSto Eg i l with
  | none =>
    cases e2 : cutSto (EgR n Eg) i l with
    | none => rfl
    | some c =>
      obtain ⟨h1, h2⟩ := cutSto_some.1 e2
      rcases h2 with h2 | h2
      · rw [cutSto_own (sto_R_sub h1) h2] at e1; cases e1
      · exact absurd h2 (nsh _ rfl)
  | some c =>
    obtain ⟨h1, h2⟩ := cutSto_some.1 e1
    rcases h2 with h2 | h2
    · refine cutSto_own (sto_R.2 ⟨h1, ?_⟩) h2
      rw [h2]; simp [liveB, hi]
    · exact absurd h2 (nsh _ rfl)

theorem cut_R {n i : Nat} {Eg : GEnv} (hi : i < n) (hpf : ∀ l, Eg.pfr l = none) (S : AllocLabel → Prop) :
    Cut (EgR n Eg) i S = Cut Eg i S := by
  unfold Cut; rw [cutSto_R hi hpf]; rfl

theorem lt_of_get {c : Cfg} {i : Nat} {th : TTh} (h : c.ths[i]? = some th) : i < c.ths.size := by
  rcases Nat.lt_or_ge i c.ths.size with hi | hi
  · exact hi
  · rw [Array.getElem?_eq_none hi] at h; cases h

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}

theorem sysInvW_R {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (hpf : ∀ l, Eg.pfr l = none)
    (hbx : ∀ l, Eg.box l = none) :
    SysInvW p k arch Init MintOK c (EgR c.ths.size Eg) Tot HP HS cr db where
  thr := by
    intro i th hth
    obtain ⟨S, hS⟩ := h.thr i th hth
    refine ⟨S, ?_⟩
    have e : Cut (EgR c.ths.size Eg) (gOf p k arch c i).i S = Cut Eg (gOf p k arch c i).i S :=
      cut_R (lt_of_get hth) hpf S
    rw [e]; exact hS
  held := by
    obtain ⟨L, Rl, hnd, h1, h2, hHS, h3⟩ := h.held
    have hL : ∀ l, l ∉ L := fun l hl => by
      obtain ⟨f, hf⟩ := h2 l hl; rw [hpf l] at hf; cases hf
    refine ⟨L, Rl, hnd, fun l cl hs _ => ?_, fun l hl => absurd hl (hL l), hHS, fun l hl => absurd hl (hL l)⟩
    obtain ⟨f, hf⟩ := hs
    have hf' : Eg.pfr l = some f := hf
    rw [hpf l] at hf'; cases hf'
  clo := fun l cl hc => h.clo l cl (sto_R_sub hc)
  cmg := fun l cl hc => h.cmg l cl (sto_R_sub hc)
  shty := fun l cl ⟨f, hf⟩ _ => by
    have hf' : Eg.pfr l = some f := hf
    rw [hpf l] at hf'; cases hf'
  proms := h.proms
  fpok := by
    intro i th S hth
    rw [cut_R (lt_of_get hth) hpf S]; exact h.fpok i th S hth
  fresh := by
    intro i th hth j hj
    obtain ⟨a, b, c1, d, e⟩ := h.fresh i th hth j hj
    exact ⟨sto_R_none a, b, c1, d, e⟩
  bal := h.bal
  tok := h.tok
  wd := h.wd
  own := h.own
  bf := h.bf
  boxtop := fun l B hB => by
    have hB' : Eg.box l = some B := hB
    rw [hbx l] at hB'; cases hB'
  disj := h.disj
  fpfree := h.fpfree
  plt := h.plt
  vwr := h.vwr
  frle := fun l cl f hc hf => h.frle l cl f (sto_R_sub hc) hf
  rle := h.rle
  bnamed := fun l B hB => by
    have hB' : Eg.box l = some B := hB
    rw [hbx l] at hB'; cases hB'
  freshU := fun q j h1 h2 => by
    obtain ⟨⟨a, b, c1, d, e⟩, o⟩ := h.freshU q j h1 h2
    exact ⟨⟨sto_R_none a, b, c1, d, e⟩, o⟩

/-- **The clean start** (J-a): `InitOK` gives `SysInvO`. -/
theorem sysInvO_of_initOK {c : Cfg} (h0 : InitOK p k arch Init MintOK c) : SysInvO p k arch Init MintOK c := by
  obtain ⟨⟨Eg, T0, H0, S0, cr0, db0, hw0, hr0, hof0, hu0, hoc0, hbx0, hpf0, hko0, hop0, hni0, hsw0, hlb0, hly0, hmem0, -, hvl0⟩,
    hn0, hcc0⟩ := h0
  have hw := sysInvW_R hw0 hpf0 hbx0
  have hpf : ∀ l, (EgR c.ths.size Eg).pfr l = none := hpf0
  have hbx : ∀ l, (EgR c.ths.size Eg).box l = none := hbx0
  refine ⟨EgR c.ths.size Eg, T0, H0, S0, cr0, db0,
    TermMain.SysInvW.toN hw hn0 hr0 hof0 (fun l cl hc => hu0 l cl (sto_R_sub hc))
      (fun i th S hth => by rw [cut_R (lt_of_get hth) hpf0 S]; exact hoc0 i th S hth) hbx
      (fun j th l hj hT => by
        rcases hko0 j th l hj hT with e | ⟨cl, e, ho⟩
        · exact Or.inl (sto_R_none e)
        · refine Or.inr ⟨cl, sto_R.2 ⟨e, ?_⟩, ho⟩
          rw [ho]; simp [liveB, lt_of_get hj])
      (fun l hl => absurd (hpf0 l) (hop0 l hl).1) (fun l cl hc => hni0 l cl (sto_R_sub hc))
      (TermUndefLow.undefLow_nil hmem0) (TermZwIni.zwIni_none hpf) (TermPredHold.predHold_none hpf) hvl0
      (fun t m cl hm _ => by rw [hmem0] at hm; simp at hm) hmem0 hpf (fun i th h => hlb0 i th h)
      (fun l cl hc => hly0 l cl (sto_R_sub hc)) hcc0 (fun l cl hc => hsw0 l cl (sto_R_sub hc)),
    ⟨fun l cl i hc ho => ?_, fun l B hB => by rw [hbx l] at hB; cases hB⟩, fun j _ => ⟨?_, ?_, ?_⟩⟩
  · have := (sto_R.1 hc).2
    rw [ho] at this; simpa [liveB] using this
  · intro l cl f _ _ hf; rw [Cut_pfr, hpf l] at hf; cases hf
  · intro l cl f o _ _ hf; rw [Cut_pfr, hpf l] at hf; cases hf
  · intro l cl f b S us o _ _ hf; rw [Cut_pfr, hpf l] at hf; cases hf

end

/-- **The run lift** (step 2): `SysInvO` at the phantom setup end. -/
theorem sysInvO_phant_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {cpre cs : Cfg} {th0 : TTh} {f : String} {ts : List Ty} {d : Decl}
    (O0 : ObligationsF p k arch Init (fun _ => True) (phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre))
    (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) cpre)
    (hpre : cpre.ths[0]? = some th0) (hstk0 : th0.stack = []) (hset : th0.term = .tail f [] (.var "a") ts)
    (hd : p.find f = .ok d)
    (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (hR0a : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hR0w : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true)
    (hrun : TermStep.Steps p k arch cpre cs) :
    SysInvO p k arch Init (fun _ => True) (phantC (f0 (substTs ts.reverse 0 0 (instT [] 0 d.retTy))) cs) := by
  have hI := initOK_phant h0 hpre hstk0 hset hd hR0 hR0a hR0w
  exact sysInvO_run (toObligationsS O0 hk (startOK_of_initOK hI)) (sysInvO_of_initOK hI) (steps_phantC hrun)

end TermSpawn

#print axioms TermSpawn.sysInvO_of_initOK
#print axioms TermSpawn.sysInvO_phant_run
