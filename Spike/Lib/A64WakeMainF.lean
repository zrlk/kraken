/-
**main's flag load facts** (AArch64): the node obligations of
main's post-spawn segments at `W := fun s c => WakeInst.FlagW lbl lsize q s c`,
`q` the pc after `waitLoop`'s `ldar` (`WCompat0.flagLd` through
`WakeInst.flagLd_I`). The loop's control `c0` is at `wlBody`, its flag word
inside its label (`Flag0`); past the load the source is at `wlIf` with `d`
read as `1`, and the parent's control is at neither (`FlagOff`). At `c0` the
state's instruction is no load of the flag's word but the `ldar` (a block
runs to `.done`, an `svc` faults, a `swpal` is an RMW, the limit load reads
`tp + 8 ≠ A`), which lands at `q` with the value in `x9`; at `q` (the loop's
`n4` node) `x9 ≠ 1`; every other pc of `c0` is off `q` (`RunsNe`, decided on
the listing at `flagRuns`).

- `FlagOff`, `Flag0`, `flag0_of`, `flagOff_past`, `flagW_mk`, `flagW_off`.
- `blkW_flag`, `nodeW_flag`, `blkW_off`, `nodeW_off`.
- `tp8_ne`: the limit word `tp + 8`, outside every placed label, is not the
  flag's word.
- `flagRuns`; `loopW_flag`, `parkGW_flag`, `parentW_flag`, `exitW0_flag`,
  `exitW1_flag`, `tlsW_flag`.
-/
import Spike.Lib.A64WakeMainL

namespace Spike.Lib.A64WakeMainF

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep LocRep)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64WakeMainSegW (ParentW exitNP)
open Spike.Lib.WakeInst (FlagW)
open Spike.Lib.WakeM0 (wlBody wlIf)
open Spike.Lib.A64WakeOff (RunsNe runsNe_add)
open Spike.Lib.A64 (CodeAt)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64} {c0 : Ctl}
  {A : BitVec 64}

/-! ## The controls -/

/-- **A control off the flag load**: not at `wlBody`, and at `wlIf` with
`d` bound to a word representing `1`. -/
def FlagOff (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) : Prop :=
  c.term ≠ wlBody ∧ (c.term = wlIf → ∀ t w', TermRun.lookupE c.env "d" = some (t, [w']) → ValRep lbl w'.val 1)

/-- **The flag load's control**: at `wlBody`, `c` bound to one untagged
locative inside its placed label, every word representing which is `A`. -/
def Flag0 (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (c0 : Ctl)
    (A : BitVec 64) : Prop :=
  c0.term = wlBody ∧ (∃ t w sa, TermRun.lookupE c0.env "c" = some (t, [w]) ∧ w.val = .loc sa 0 ∧
    (lbl sa.label).isSome ∧ sa.offset < lsize sa.label) ∧
  ∀ t w (A' : BitVec 64), TermRun.lookupE c0.env "c" = some (t, [w]) → ValRep lbl w.val A'.toNat → A' = A

theorem wlBody_ne_wlIf : wlBody ≠ wlIf := by
  intro h; unfold wlBody wlIf at h; cases h

/-- `wlBody`'s load binds `d` from `c` and continues at `wlIf`. -/
theorem shape_of {x : String} {a : At} {e : Expr} (hwb : c0.term = wlBody)
    (hterm : c0.term = .let_ x (.load true a) e) : x = "d" ∧ a = .var "c" ∧ e = wlIf := by
  rw [hwb] at hterm; unfold wlBody at hterm; cases hterm; exact ⟨rfl, rfl, rfl⟩

/-- **`Flag0` at the loop's control**: at `wlBody` (`hwb`), its load's word
`w` an untagged locative with base `A` (`hloc`), inside its label (`hin`). -/
theorem flag0_of {x : String} {a : At} {e : Expr} {ty : Ty} {w : TermRun.Word} (hwb : c0.term = wlBody)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    Flag0 lbl lsize c0 A := by
  obtain ⟨-, rfl, -⟩ := shape_of hwb hterm
  have hl : TermRun.lookupE c0.env "c" = some (ty, [w]) := hev
  obtain ⟨sa, hw, hsz⟩ := hin
  rw [hw] at hloc
  obtain ⟨-, hb, ho⟩ := hloc
  refine ⟨hwb, ⟨ty, w, sa, hl, hw, by rw [hb]; rfl, hsz⟩, fun t w' A' hl' hv => ?_⟩
  rw [hl] at hl'
  cases hl'
  rw [hw] at hv
  obtain ⟨-, y, hy, hA'⟩ := hv
  have hy' : (lbl sa.label).map (· + 8 * sa.offset) = some y := hy
  rw [hb, Option.map_some, Option.some.injEq] at hy'
  have h1 : @Eq Nat 0 (8 * sa.offset) := ho
  have h2 : @Eq Nat (A.toNat + 8 * sa.offset) y := hy'
  have h3 : @Eq Nat A'.toNat (y + 0) := hA'
  exact BitVec.eq_of_toNat_eq (by omega)

/-- **Past the load the control is off it**: at `wlIf`, `d` read as `1`. -/
theorem flagOff_past {x : String} {a : At} {e : Expr} {ty : Ty} {ms : MemSide isaLSE2} {c : Ctl}
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (h : Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c) :
    FlagOff lbl c := by
  obtain ⟨rfl, -, rfl⟩ := shape_of hwb hterm
  obtain ⟨w', ⟨-, hw'⟩, rfl⟩ := h
  refine ⟨fun h => wlBody_ne_wlIf h.symm, fun _ t w'' hl => ?_⟩
  simp only [TermRun.lookupE, List.find?, beq_self_eq_true, Option.map_some, Option.some.injEq,
    Prod.mk.injEq, List.cons.injEq, and_true] at hl
  obtain ⟨-, rfl⟩ := hl
  exact hw'

/-- **`FlagW` from its pieces**: the control `c0` or off the flag load; at
`c0`, a load of `A` lands at `q` with the value in `x9` (`hG`), and at `q`
`x9 ≠ 1` (`hX`). -/
theorem flagW_mk {s : State} {c : Ctl} (h0 : Flag0 lbl lsize c0 A) (hc : c = c0 ∨ FlagOff lbl c)
    (hG : c = c0 → ∀ kl (k' : Val → EvTree State), isaLSE2.exec s = some (.load kl false ⟨A, 8⟩ k') →
      ∀ v, ∃ s', k' v = .done s' ∧ s'.st.2 = q ∧ (s'.st.1.regs.getXReg .X9).toBitVec = v.setWidth 64)
    (hX : c = c0 → s.st.2 = q → (s.st.1.regs.getXReg .X9).toBitVec ≠ 1#64) : FlagW lbl lsize q s c := by
  unfold FlagW
  rcases hc with rfl | ⟨hb, hE⟩
  · obtain ⟨hwb, hA, hu⟩ := h0
    refine ⟨fun h => absurd (hwb.symm.trans h) wlBody_ne_wlIf, fun _ => hA,
      fun _ t w A' kl k' hl hv he => ?_, fun _ => hX rfl⟩
    obtain rfl := hu t w A' hl hv
    exact hG rfl kl k' he
  · exact ⟨hE, fun h => absurd h hb, fun h => absurd h hb, fun h => absurd h hb⟩

/-- **`FlagW` off the flag load.** -/
theorem flagW_off {s : State} {c : Ctl} (h : FlagOff lbl c) : FlagW lbl lsize q s c :=
  ⟨h.2, fun e => absurd e h.1, fun e => absurd e h.1, fun e => absurd e h.1⟩

/-- **A pc of a run is not `q`** (`k = 0` form of `runsNe_add`). -/
theorem runsNe_at {lab : String → Int64} {runs : List (String × Nat × Nat)} (h : RunsNe lab q runs)
    {l : String} {lo hi c : Nat} (hq : (l, lo, hi) ∈ runs) (h1 : lo ≤ c) (h2 : c < hi) {p : Int64}
    (hp : p = lab l + Int64.ofNat (4 * c)) : p ≠ q := by
  subst hp; exact h _ hq c h1 h2

/-! ## Blocks and nodes -/

/-- **A covered block's states are in `FlagW`**: they run to `.done`; their
controls are `c0` or off the flag load, and at `c0` `x9 ≠ 1` wherever the pc
is `q` (`hX`). -/
theorem blkW_flag {n : ND} {lo hi : Int} {blk : List Directive} (hok : okBlk lo hi n.o blk = true) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) (h0 : Flag0 lbl lsize c0 A)
    (hc : ∀ σ c, n.J σ c → c = c0 ∨ FlagOff lbl c)
    (hX : ∀ σ k m, n.J σ c0 → k < blk.length →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      n.pc + Int64.ofNat (4 * k) = q → (m.regs.getXReg .X9).toBitVec ≠ 1#64) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA _
  subst he
  obtain ⟨s', hx⟩ := blk_exec_done hok hR hal hlo hhi (hcode s rfl hn) hk hA
  refine ⟨flagW_mk h0 (hc σ c hJ) (fun _ _ _ h => by rw [hx] at h; cases h) fun hc0 hq => ?_, fun _ h => h⟩
  subst hc0
  exact hX σ k m hJ hk hA hq

/-- **A node's states are in `FlagW`**: controls `c0` or off the flag load;
at `c0`, `hG` and `hX` of `flagW_mk`. -/
theorem nodeW_flag {n : ND} (h0 : Flag0 lbl lsize c0 A) (hc : ∀ σ c, n.J σ c → c = c0 ∨ FlagOff lbl c)
    (hG : ∀ s, At exe endPc R F n s c0 → ∀ kl (k' : Val → EvTree State),
      isaLSE2.exec s = some (.load kl false ⟨A, 8⟩ k') →
      ∀ v, ∃ s', k' v = .done s' ∧ s'.st.2 = q ∧ (s'.st.1.regs.getXReg .X9).toBitVec = v.setWidth 64)
    (hX : ∀ s, At exe endPc R F n s c0 → s.st.2 = q → (s.st.1.regs.getXReg .X9).toBitVec ≠ 1#64) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := id hAt
  exact ⟨flagW_mk h0 (hc σ c hJ) (fun h => by subst h; exact hG s hAt) (fun h => by subst h; exact hX s hAt),
    fun _ h => h⟩

/-- **A block whose controls are off the flag load.** -/
theorem blkW_off {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → FlagOff lbl c) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
  exact ⟨flagW_off (h σ c hJ), fun _ h => h⟩

/-- **A node whose controls are off the flag load.** -/
theorem nodeW_off {n : ND} (h : ∀ σ c, n.J σ c → FlagOff lbl c) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨flagW_off (h σ c hJ), fun _ h => h⟩

/-- An `svc` is no load. -/
theorem svc_noLoad {s : State} {imm sz : Nat} (hc : CellAt s (.instr ⟨.W64, .SVC imm⟩) sz) {kl : LoadKind} {L : Loc}
    {k' : Val → EvTree State} : isaLSE2.exec s ≠ some (.load kl false L k') := by
  rw [exec_svc hc]; intro h; cases h

/-- A `swp` is no load. -/
theorem swp_noLoad {s : State} {sz : Nat} {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt s (.instr ⟨.W64, .SWP k .W64 rs rt (.low (.reg n) .W64)⟩) sz) {kl : LoadKind} {L : Loc}
    {k' : Val → EvTree State} : isaLSE2.exec s ≠ some (.load kl false L k') := by
  cases hm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg n).toBitVec 8 with
  | none =>
    rw [exec_swp hc hm]; intro h
    have h' := Option.some.inj h
    unfold EvTree.access at h'
    split at h' <;> cases h'
  | some j =>
    obtain ⟨s', h'⟩ := exec_swp_mapped hc hm
    rw [h']; intro h; cases h

/-- **The limit word is not the flag's**: `tp + 8` is outside every placed
label (`hrt`, `Ret0.LimOk.rt` under `MemSide.ofLabels`), the flag's word `A`
the base of its label `w`, which has a word (`hin`). -/
theorem tp8_ne {tp : BitVec 64} {w : TermRun.Word}
    (hrt : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains (tp + 8#64).toNat)
    (hloc : LocRep lbl w.val A.toNat 0) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    tp + 8#64 ≠ A := by
  intro h
  obtain ⟨sa, hw, hsz⟩ := hin
  rw [hw] at hloc
  obtain ⟨-, hb, -⟩ := hloc
  have h1 : @LT.lt Nat _ sa.offset (lsize sa.label) := hsz
  refine hrt ⟨sa.label, A.toNat, hb, ?_⟩
  show A.toNat ≤ (tp + 8#64).toNat ∧ (tp + 8#64).toNat < A.toNat + 8 * lsize sa.label
  rw [h]; omega

/-! ## main's post-spawn nodes -/

/-- **main's pcs at the flag load's control other than `q`**: `waitRuns`
without `q` (cell `2` of `.0_entry`; `.1_then1` is past the load) and
`scc_rt_park`'s. -/
def flagRuns (pfx : String) : List (String × Nat × Nat) :=
  [("wc_waitLoop", 0, 10), (pfx ++ ".0_entry", 0, 2), (pfx ++ ".0_entry", 3, 8), (pfx ++ ".2_else2", 0, 1),
    (pfx ++ ".sp3", 0, 5)] ++ Spike.Lib.A64.Flow.Park.parkRuns

set_option hygiene false in
/-- A block's `hX` from `flagRuns`: the run `(l, lo, hi)`, the node's offset
`c` in it, the block's definitions. -/
macro "ne_blk " l:term:max lo:term:max hi:term:max c:term:max "[" bs:ident,* "]" : tactic =>
  `(tactic| (intro _ k _ _ hk _ hq
             simp only [$[$bs:ident],*, List.length_append, List.length_cons, List.length_nil] at hk
             exact absurd hq <| runsNe_add (l := $l) (lo := $lo) (hi := $hi) (c := $c) hflag
               (by simp [flagRuns, Spike.Lib.A64.Flow.Park.parkRuns]) (by omega) (by omega)
               (by simp only [Spike.Lib.A64.WaitLoop.N, Spike.Lib.A64.Flow.Park.N, Spike.Lib.A64.Flow.Park.pcSvc,
                     Int64.add_assoc]; first | rfl | simp | decide)))

section Loop

open Spike.Lib.A64.WaitLoop

variable {pfx : String} {x : String} {a : At} {e : Expr} {ty : Ty} {w : TermRun.Word} {ms : MemSide isaLSE2}
  {x29 ra tp : BitVec 64}

/-- **`wc_waitLoop`'s states are in `FlagW`** (`LoopW`), `q` the `n4`
node's pc: the loop's control at `wlBody` (`hwb`), its load's word `w` the
untagged locative with base `A` inside its label (`hloc`, `hin`), and every
pc of `c0` but `q` off `q` (`hflag`). -/
theorem loopW_flag (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hcode : Code pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp exe endPc)
    (hq : q = (_root_.Executable.labels exe).label (pfx ++ ".0_entry") + 4 + 4)
    (hflag : RunsNe (_root_.Executable.labels exe).label q (flagRuns pfx))
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c0.env a = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    LoopW (fun s c => FlagW lbl lsize q s c) exe endPc R F pfx c0 x e ty
      (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp := by
  have h0 := flag0_of (lsize := lsize) hwb hterm hev hloc hin
  have hP := fun c => flagOff_past (lbl := lbl) (ty := ty) (ms := ms) (c := c) hwb hterm
  have hnp : ¬ Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c0 := fun h =>
    (hP c0 h).1 hwb
  refine {
    top := blkW_flag b0_ok hR hal hlo hhi hcode.top h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk "wc_waitLoop" 0 10 0 [b0])
    n1 := blkW_flag b1_ok hR hal hlo hhi hcode.n1 h0 (fun _ _ hJ => .inl hJ.1.1)
      (by ne_blk "wc_waitLoop" 0 10 3 [b1, b1p])
    n2 := blkW_flag b2_ok hR hal hlo hhi hcode.n2 h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk "wc_waitLoop" 0 10 5 [b2])
    entry := blkW_flag b3_ok hR hal hlo hhi hcode.entry h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk (pfx ++ ".0_entry") 0 2 0 [b3])
    ld := nodeW_flag h0 (fun _ _ hJ => .inl hJ.1.1) (fun s ⟨he, hn, hdc, hpc, σ, hA, _, hJ⟩ kl k' hx v => ?_)
      fun s ⟨_, _, _, hpc, _⟩ hq' => absurd hq' <| runsNe_at hflag (p := s.st.2) (l := pfx ++ ".0_entry") (lo := 0) (hi := 2) (c := 1)
        (by simp [flagRuns]) (by omega) (by omega) (by rw [hpc]; simp only [N]; first | rfl | simp)
    n4 := blkW_flag b4_ok hR hal hlo hhi hcode.n4 h0
      (fun _ c hJ => by
        obtain ⟨-, -, ⟨-, hp⟩ | ⟨-, rfl⟩⟩ := hJ
        · exact .inr (hP c hp)
        · exact .inl rfl)
      (fun σ k m hJ hk hA hpq => by
        rcases k with _ | k
        · obtain ⟨-, -, ⟨-, hp⟩ | ⟨h9, -⟩⟩ := hJ
          · exact (hnp hp).elim
          · rw [hA.regs]; exact h9
        · simp only [b4, b4p, List.length_append, List.length_cons, List.length_nil] at hk
          have hne := runsNe_add (l := pfx ++ ".0_entry") (lo := 3) (hi := 8) (c := 3) (k := k) hflag
            (by simp [flagRuns]) (by omega) (by omega) (p := (_root_.Executable.labels exe).label (pfx ++ ".0_entry") +
              Int64.ofNat (4 * 3)) rfl
          refine absurd (Eq.trans ?_ hpq) hne
          simp only [N, Int64.add_assoc]
          congr 1
          show Int64.ofNat _ + Int64.ofNat _ = Int64.ofNat 4 + (Int64.ofNat 4 + Int64.ofNat _)
          rw [← Int64.ofNat_add, ← Int64.ofNat_add, ← Int64.ofNat_add]
          congr 1
          omega)
    n5 := blkW_flag b5_ok hR hal hlo hhi hcode.n5 h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk (pfx ++ ".0_entry") 3 8 7 [b5])
    then1 := blkW_flag b6_ok hR hal hlo hhi hcode.then1 h0 (fun _ c hJ => .inr (hP c hJ.2.2.1))
      (fun _ _ _ hJ => (hnp hJ.2.2.1).elim)
    else2 := blkW_flag b7_ok hR hal hlo hhi hcode.else2 h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk (pfx ++ ".2_else2") 0 1 0 [b7])
    sp3 := blkW_flag b8_ok hR hal hlo hhi hcode.sp3 h0 (fun _ _ hJ => .inl hJ.1)
      (by ne_blk (pfx ++ ".sp3") 0 5 0 [b8]) }
  -- the `ldar`
  have hc : CellAt s (ldarDir .X9 .X10) 4 := (hcode.ld s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  cases hm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg .X10).toBitVec 8 with
  | some j => rw [exec_ldar_mapped hc hm] at hx; cases hx
  | none =>
    rw [exec_ldar_agrees hc hm (agrees_of_decls hdc _ _)] at hx
    simp only [Option.some.injEq, ] at hx
    obtain ⟨-, -, -, rfl⟩ := hx
    refine ⟨_, rfl, ?_, ?_⟩
    · show s.st.2 + Int64.ofNat 4 = q
      rw [hpc, hq]; simp only [N]; rfl
    · simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.getXReg]

/-- **The exit tail's block is in `FlagW`**: past the load. -/
theorem exitW0_flag (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret) (exitTail 8) :=
  blkW_off fun _ _ hJ => flagOff_past hwb hterm hJ.1

/-- **The exit tail's `svc` state is in `FlagW`**: past the load. -/
theorem exitW1_flag (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (exitNP (E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret)) :=
  nodeW_off fun _ _ ⟨_, _, hJ, _⟩ => flagOff_past hwb hterm hJ.1

/-- **`wc_waitLoop`'s limit load is in `FlagW`**: it loads `tp + 8`, not the
flag's word (`htp8`), at a pc off `q`. -/
theorem tlsW_flag [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
    (hend : endPc = endOf exe wakeProg kp)
    (hpc : (N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls).pc =
      (_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hflag : RunsNe (_root_.Executable.labels exe).label q (flagRuns Spike.Lib.A64.WakeLabels.pfx))
    (htp8 : tp + 8#64 ≠ A) (h0 : Flag0 lbl lsize c0 A) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls) := by
  refine nodeW_flag h0 (fun _ _ hJ => .inl hJ.1.1) (fun s ⟨he, hn, hdc, hs, σ, hA, _, hJ⟩ kl k' hx => ?_)
    fun s ⟨_, _, _, hs, _⟩ hq' => absurd hq' <| runsNe_at hflag (p := s.st.2) (l := "wc_waitLoop") (lo := 0) (hi := 10) (c := 2)
      (by simp [flagRuns]) (by omega) (by omega) (by rw [hs]; simp only [N, Int64.add_assoc]; first | rfl | simp)
  have hcell : CellAt s (ldrDir .X10 .X10 8) 4 :=
    (code_of hp hend Spike.Lib.A64.Flow.Worker.Wake.AbOffAt.wait_tlsCode hpc.symm s he hn).cell (j := 0) rfl rfl
      rfl (by rw [hs]; simp)
  have ha : rAddr s.st.1.regs .X10 8 = tp + 8#64 := by
    rw [hA.regs]; exact Spike.Lib.A64.Flow.Ret0.rAddr_x10 hJ.2 8
  cases hm : Mem.loadInt s.st.1.dmem (tp + 8#64) 8 with
  | some j => rw [exec_ldr_mapped hcell ha hm] at hx; cases hx
  | none =>
    rw [exec_ldr_agrees hcell ha hm (agrees_of_decls hdc _ _)] at hx
    injection hx with hx
    injection hx with _ _ hL
    injection hL with hA
    exact (htp8 hA).elim

end Loop

section Park

open Spike.Lib.A64.Flow.Park

/-- **`scc_rt_park`'s states are in `FlagW`**: their control is the loop's
`c0`, their instructions no load of the flag's word (blocks, `swpal`s, the
`svc`), their pcs off `q` (`hflag`). -/
theorem parkGW_flag {pfx : String} {x29 ra tp : BitVec 64} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -64) (hhi : 0 ≤ R.hi) (hcode : Code c0 x29 ra tp exe endPc)
    (hflag : RunsNe (_root_.Executable.labels exe).label q (flagRuns pfx)) (h0 : Flag0 lbl lsize c0 A) :
    ParkGW (fun s c => FlagW lbl lsize q s c) exe endPc R F c0 x29 ra tp := by
  have hc : ∀ {n : ND}, (∀ σ c, n.J σ c → c = c0) → ∀ σ c, n.J σ c → c = c0 ∨ FlagOff lbl c :=
    fun h σ c hJ => .inl (h σ c hJ)
  exact {
    e := blkW_flag b0_ok hR hal hlo hhi hcode.e h0 (hc fun _ _ h => h.1)
      (by ne_blk "scc_rt_park" 0 4 0 [b0])
    n1 := blkW_flag b1_ok hR hal hlo hhi hcode.n1 h0 (hc fun _ _ h => h.1)
      (by ne_blk ".L10_scc_rt_park.0_entry" 0 12 0 [b1])
    swp1 := nodeW_flag h0 (hc fun _ _ h => h.1.1.1)
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (swp_noLoad ((hcode.swp1 s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hpc]; simp)) hx).elim)
      fun s ⟨_, _, _, hpc, _⟩ hq' => absurd hq' <| runsNe_at hflag (p := s.st.2) (l := ".L10_scc_rt_park.0_entry") (lo := 0) (hi := 12) (c := 5)
        (by simp [flagRuns, parkRuns]) (by omega) (by omega) (by rw [hpc]; simp only [N, Int64.add_assoc]; first | rfl | simp)
    n2 := blkW_flag b2_ok hR hal hlo hhi hcode.n2 h0 (hc fun _ _ h => h.1.1)
      (by ne_blk ".L10_scc_rt_park.0_entry" 0 12 6 [b2])
    n3 := blkW_flag b3_ok hR hal hlo hhi hcode.n3 h0 (hc fun _ _ h => h.1.1)
      (by ne_blk ".L10_scc_rt_park.0_entry" 0 12 11 [b3])
    wait := blkW_flag b4_ok hR hal hlo hhi hcode.wait h0 (hc fun _ _ h => h.1.1)
      (by ne_blk ".L10_scc_rt_park.1_wait" 0 22 0 [b4])
    svc := nodeW_flag h0 (hc fun _ _ h => h.1.1.1)
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (svc_noLoad ((hcode.svc s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hpc]; simp)) hx).elim)
      fun s ⟨_, _, _, hpc, _⟩ hq' => absurd hq' <| runsNe_at hflag (p := s.st.2) (l := ".L10_scc_rt_park.1_wait") (lo := 0) (hi := 22) (c := 11)
        (by simp [flagRuns, parkRuns]) (by omega) (by omega)
        (by rw [hpc]; simp only [N, pcSvc, Int64.add_assoc]; first | rfl | simp)
    n5 := blkW_flag b5_ok hR hal hlo hhi hcode.n5 h0 (hc fun _ _ h => h.1.1)
      (by ne_blk ".L10_scc_rt_park.1_wait" 0 22 12 [b5])
    swp2 := nodeW_flag h0 (hc fun _ _ h => h.1.1.1)
      (fun s ⟨he, hn, _, hpc, _⟩ _ _ hx => (swp_noLoad ((hcode.swp2 s he hn).cell (j := 0) rfl rfl rfl
        (by rw [hpc]; simp)) hx).elim)
      fun s ⟨_, _, _, hpc, _⟩ hq' => absurd hq' <| runsNe_at hflag (p := s.st.2) (l := ".L10_scc_rt_park.1_wait") (lo := 0) (hi := 22) (c := 16)
        (by simp [flagRuns, parkRuns]) (by omega) (by omega)
        (by rw [hpc]; simp only [N, pcSvc, Int64.add_assoc]; first | rfl | simp)
    n6 := blkW_flag b6_ok hR hal hlo hhi hcode.n6 h0 (hc fun _ _ h => h.1.1)
      (by ne_blk ".L10_scc_rt_park.1_wait" 0 22 17 [b6])
    done := blkW_flag b7_ok hR hal hlo hhi hcode.done h0 (hc fun _ _ h => h.1.1)
      (by ne_blk ".L10_scc_rt_park.2_done" 0 4 0 [b7]) }

end Park

/-- **The parent's states are in `FlagW`**: its control `cP` is at neither
`wlBody` nor `wlIf` (`hcPf`). -/
theorem parentW_flag {cP : Ctl} {A x29 ra tp : BitVec 64} (hcPf : cP.term ≠ wlBody ∧ cP.term ≠ wlIf) :
    ParentW (fun s c => FlagW lbl lsize q s c) exe endPc R F cP A x29 ra tp :=
  have hP : FlagOff lbl cP := ⟨hcPf.1, fun h => absurd h hcPf.2⟩
  { wcb := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wcl := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wbs := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
    wsp := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP }

/-- info: 'Spike.Lib.A64WakeMainF.loopW_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopW_flag
/-- info: 'Spike.Lib.A64WakeMainF.parkGW_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parkGW_flag
/-- info: 'Spike.Lib.A64WakeMainF.tlsW_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tlsW_flag
/-- info: 'Spike.Lib.A64WakeMainF.tp8_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tp8_ne

end Spike.Lib.A64WakeMainF
