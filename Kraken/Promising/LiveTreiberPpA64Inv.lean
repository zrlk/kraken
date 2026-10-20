/-
**One step of a `treiber_pp` thread, and the trace
invariant, on the semantic machine** (AArch64, `Arch.armv8`, any
declarations agreeing on `top`, the node's data word and its link word).

Thread `0` (role `r = 0`) is the pusher, at positions `1 … 9` and its end
`11`; thread `1` is the popper, at `13 … 22` and its end `24`
(`LiveTreiberPpA64Trees.lean`). `StepOK` says what one instruction step does:
the next position (`nextP`), the registers the walks of
`LiveTreiberPpA64.lean` follow (`X2` kept off the loads of `top`; the loads
of `top` and the `CASAL`s return `top`'s final value once the thread's
coherence view has reached `top`'s last write), and the effect on memory and
promises, with the thread's successful `CASAL`s `S` (`sOf`) growing by one
exactly at a write to `top`; the pusher writes `top` only with its node, the
popper writes only `top` (`Q`). The invariant `Inv` (the `LiveTermTreiber2P`
recipe) adds the promise bounds, `Q` for every outstanding promise
(`promGood_of_certOkN`), the count of writes to `top` and the pusher's node in
`top` once the pusher succeeded.
-/
import Kraken.Promising.LiveTreiberPpA64Trees
import Kraken.Promising.LiveTreiberPpSkel
import Kraken.Promising.LiveTermTreiber2P

namespace Kraken.Promising.Live.TreiberPpA64

set_option linter.unusedSectionVars false

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Term
open Kraken.Promising.SLR.EnvG.Treiber (treiberImageA)
open Kraken.Promising.SLR.A64Trees (goto)
open Kraken.Promising.Live.TicketStep (spec_done spec_load)
open Kraken.Promising.Live.SemShape (spec_store_p)

/-- `top`. -/
abbrev topL (t : BitVec 64) : Loc := ⟨t, 8⟩

/-- The successful `CASAL`s of a thread at position `p` (`0` or `1`). -/
def sOf (p : Nat) (s : MachineData) : Nat :=
  if p = 7 ∨ p = 18 then (if s.regs.X3.toBitVec = s.regs.X2.toBitVec then 1 else 0)
  else if p = 8 ∨ p = 19 then (if s.status.z = true then 1 else 0)
  else if p = 9 ∨ p = 11 ∨ p = 20 ∨ p = 21 ∨ p = 22 ∨ p = 24 then 1 else 0

/-- The position after the cell at `p`. -/
def nextP (p : Nat) (s : MachineData) : Nat :=
  match p with
  | 1 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8
  | 8 => if s.status.z = true then 9 else 3
  | 9 => 11 | 13 => 14
  | 14 => if s.regs.X2.toBitVec = 0#64 then 13 else 15
  | 15 => 16 | 16 => 17 | 17 => 18 | 18 => 19
  | 19 => if s.status.z = true then 20 else 13
  | 20 => 21 | 21 => 22 | 22 => 24
  | _ => 0

/-- The register fact at a position: `X3 = X2` at the `CASAL`s. -/
def PcI (s : MachineData) (i : Nat) : Prop := (i = 6 ∨ i = 17) → s.regs.X3.toBitVec = s.regs.X2.toBitVec

/-- A role's end position. -/
def endP (r : Nat) : Nat := if r = 0 then 11 else 24

/-- A role's positions. -/
def pcsR (r : Nat) : List Nat :=
  if r = 0 then [1, 3, 4, 5, 6, 7, 8, 9, 11] else [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24]

theorem mem_tPcs {r i : Nat} (h : i ∈ pcsR r) : i ∈ tPcs := by
  unfold pcsR at h
  split at h <;> simp only [tPcs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢ <;> omega

theorem role0 {r i : Nat} (h : i ∈ pcsR r) (hi : i < 12) : r = 0 := by
  by_cases h0 : r = 0
  · exact h0
  · simp only [pcsR, h0, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem role1 {r i : Nat} (h : i ∈ pcsR r) (hi : 12 < i) : r ≠ 0 := by
  rintro rfl
  simp only [pcsR, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- What a pusher's (`2`-byte private words) or popper's write may be. -/
def Q (n t : BitVec 64) (r : Nat) (w : Msg) : Prop :=
  if r = 0 then (w.loc = topL t → w.val = BitVec.setWidth 128 n) else w.loc = topL t

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiberImageA)]

set_option hygiene false in
local notation "pcT" => (layout treiberImageA).addrOf

/-- What a thread's state never changes. -/
structure Static (ds : Decls) (t n : BitVec 64) (r : Nat) (s : isa.State) : Prop where
  exe : s.exe = layout treiberImageA
  decls : s.decls = ds
  endPc : s.endPc = pcT (endP r)
  x0 : s.st.1.regs.X0.toBitVec = t
  dt : Mem.loadInt s.st.1.dmem t 8 = none
  x1 : r = 0 → s.st.1.regs.X1.toBitVec = n
  dd : r = 0 → Mem.loadInt s.st.1.dmem n 4 = none
  dn : r = 0 → Mem.loadInt s.st.1.dmem (n + 8#64) 8 = none
  d4 : r ≠ 0 → ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- The thread sits at one of its role's positions, with its register fact. -/
def PcOK (r : Nat) (s : isa.State) : Prop := ∃ i ∈ pcsR r, s.st.2 = pcT i ∧ PcI s.st.1 i

/-- A thread's position. -/
def pos (u : Thread isa) : Nat := posOf u.st.st.2

/-- A thread's successful `CASAL`s. -/
def S (u : Thread isa) : Nat := sOf (pos u) u.st.st.1

/-- **What one instruction step of a thread does.** -/
structure StepOK (ds : Decls) (t n : BitVec 64) (r : Nat) (u : Thread isa) (mem : Memory) (o : Outcome isa) :
    Prop where
  st : Static ds t n r o.thread.st
  pc : PcOK r o.thread.st
  nx : pos o.thread = nextP (pos u) u.st.st.1
  x2 : pos u ≠ 3 → pos u ≠ 13 → o.thread.st.st.1.regs.X2 = u.st.st.1.regs.X2
  ld : pos u = 3 ∨ pos u = 13 → mem.lastWrite (topL t) ≤ u.views.getCoh (topL t) →
    o.thread.st.st.1.regs.X2.toBitVec = BitVec.setWidth 64 (mem.finalVal (topL t))
  cas : pos u = 6 ∨ pos u = 17 → mem.lastWrite (topL t) ≤ u.views.getCoh (topL t) →
    o.thread.st.st.1.regs.X3.toBitVec = BitVec.setWidth 64 (mem.finalVal (topL t))
  eff : (o.mem = mem ∧ o.thread.prom = u.prom ∧ S o.thread = S u) ∨
    (∃ w, WEff mem o.mem u.prom o.thread.prom w ∧ S o.thread = S u + (if w.loc = topL t then 1 else 0) ∧ Q n t r w)

/-! ## One step -/

section Steps

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64) {r : Nat} {u : Thread isa} {tid : Nat} {mem : Memory}
  {outs : List (Except String (Outcome isa))} {o : Outcome isa}
  (hS : Static ds t n r u.st) (hs : stepOne Arch.armv8 u tid mem = some outs) (ho : .ok o ∈ outs)

theorem Static.at {s : isa.State} (h : Static ds t n r s) {i : Nat} (hi : i ∈ pcsR r) (he : i ≠ endP r)
    (hpc : s.st.2 = pcT i) : AtD s i :=
  ⟨h.exe, hpc, by
    rw [hpc, h.endPc, beq_eq_false_iff_ne]
    exact fun e => he (addrOf_inj (mem_tPcs hi) (by unfold endP; split <;> decide) e)⟩

/-- At the end address the thread has halted. -/
theorem exec_end {s : isa.State} (h : Static ds t n r s) (hpc : s.st.2 = pcT (endP r)) : isa.exec s = none := by
  show AArch64.exec s = none
  unfold AArch64.exec
  rw [hpc, h.endPc]
  simp

/-- At the end address a thread has no step. -/
theorem stepOne_end' {s : Thread isa} (h : Static ds t n r s.st) (hpc : s.st.st.2 = pcT (endP r)) (A : Arch)
    (tid : Nat) (mem : Memory) : stepOne A s tid mem = none := by
  simp [stepOne, exec_end h hpc]

include hS hs ho

omit hS hs ho in
/-- **Assembling `StepOK`** from the cell's effect, at concrete positions. -/
theorem mk {i j : Nat} (hS : Static ds t n r u.st) (hpc : u.st.st.2 = pcT i) (hi : i ∈ pcsR r)
    {md : MachineData} (hst : o.thread.st = goto u.st md (pcT j)) (hj : j ∈ pcsR r)
    (hnx : nextP i u.st.st.1 = j) (h0 : md.regs.X0 = u.st.st.1.regs.X0) (h1 : md.regs.X1 = u.st.st.1.regs.X1)
    (hd : md.dmem = u.st.st.1.dmem) (hI : PcI md j)
    (hx2 : i ≠ 3 → i ≠ 13 → md.regs.X2 = u.st.st.1.regs.X2)
    (hld : i = 3 ∨ i = 13 → mem.lastWrite (topL t) ≤ u.views.getCoh (topL t) →
      md.regs.X2.toBitVec = BitVec.setWidth 64 (mem.finalVal (topL t)))
    (hcas : i = 6 ∨ i = 17 → mem.lastWrite (topL t) ≤ u.views.getCoh (topL t) →
      md.regs.X3.toBitVec = BitVec.setWidth 64 (mem.finalVal (topL t)))
    (heff : (o.mem = mem ∧ o.thread.prom = u.prom ∧ sOf j md = sOf i u.st.st.1) ∨
      (∃ w, WEff mem o.mem u.prom o.thread.prom w ∧
        sOf j md = sOf i u.st.st.1 + (if w.loc = topL t then 1 else 0) ∧ Q n t r w)) :
    StepOK ds t n r u mem o := by
  have pu : pos u = i := by rw [pos, hpc, posOf_pcT (mem_tPcs hi)]
  have po : pos o.thread = j := by rw [pos, hst, posOf_pcT (mem_tPcs hj)]
  have so : S o.thread = sOf j md := by rw [S, po, hst]
  have su : S u = sOf i u.st.st.1 := by rw [S, pu]
  refine ⟨by rw [hst]; exact ⟨hS.exe, hS.decls, hS.endPc, h0 ▸ hS.x0, hd ▸ hS.dt, h1 ▸ hS.x1, hd ▸ hS.dd,
    hd ▸ hS.dn, hd ▸ hS.d4⟩, ⟨j, hj, by rw [hst], by rw [hst]; exact hI⟩, by rw [po, pu, hnx],
    fun a b => by rw [hst]; exact hx2 (pu ▸ a) (pu ▸ b), fun a b => by rw [hst]; exact hld (pu ▸ a) b,
    fun a b => by rw [hst]; exact hcas (pu ▸ a) b, ?_⟩
  rw [so, su]; exact heff

omit hS in
/-- An access through the declarations: a fault has no outcome. -/
theorem access_ok {a : BitVec 64} {sz : Nat} {k : Loc → EvTree isa.State}
    (hex : isa.exec u.st = some (EvTree.access u.st.decls a sz k)) :
    ∃ l, isa.exec u.st = some (k l) := by
  unfold EvTree.access at hex
  split at hex
  · exact ⟨_, hex⟩
  · obtain ⟨_, _, hr, -⟩ := TicketStep.stepOne_out Arch.armv8 tid hex hs ho
    simp [runTree] at hr

include hT hD hN htn

/-- **One instruction step of a thread**, by position. -/
theorem thread_step (hpc : PcOK r u.st) : StepOK ds t n r u mem o := by
  obtain ⟨i, hi, hpc, hI⟩ := hpc
  have hat := fun (he : i ≠ endP r) => hS.at hi he hpc
  have hdT : u.st.decls.AgreesAt t 8 := by rw [hS.decls]; exact hT
  have hz := fun (h : i < 12) => role0 hi h
  have hnz := fun (h : 12 < i) => role1 hi h
  have hil : i ∈ [1, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24] := mem_tPcs hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hil
  have hlt : t ≠ n + 8#64 := htn
  have hloc : ¬ ((⟨n + 8#64, 8⟩ : Loc) = topL t) := fun e => hlt (by cases e; rfl)
  have e1 : r ≠ 0 → endP r = 24 := fun h => by simp [endP, h]
  have p1 : r ≠ 0 → pcsR r = [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24] := fun h => by simp [pcsR, h]
  rcases hil with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · -- 1: `STR W9,[X1]`
    obtain rfl := hz (by decide)
    obtain ⟨hst, h⟩ := spec_store_p _ _ (exec_str1 _ (hat (by decide)) (by rw [hS.decls]; exact hD)
      (hS.x1 rfl) (hS.dd rfl)) hs ho
    exact mk hS hpc hi hst (by decide) rfl rfl rfl rfl (by simp [PcI]) (fun _ _ => rfl) (by simp) (by simp)
      (.inr ⟨_, WEff.of_store h, by simp [sOf, topL], by simp [Q, topL]⟩)
  · -- 3: `LDAR X2,[X0]`
    obtain rfl := hz (by decide)
    obtain ⟨k, hex⟩ := exec_ldar 3 (.inl rfl) _ (hat (by decide)) hdT hS.x0 hS.dt
    obtain ⟨ts, v, hst, -, hlw, hm, hp, -⟩ := spec_load _ _ hex hs ho
    exact mk hS hpc hi hst (by decide) rfl rfl rfl rfl (by simp [PcI]) (by simp) (fun _ hl => by simp [hlw hl])
      (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 4: `STR X2,[X1,#8]`
    obtain rfl := hz (by decide)
    obtain ⟨hst, h⟩ := spec_store_p _ _ (exec_str4 _ (hat (by decide)) (by rw [hS.decls]; exact hN)
      (hS.x1 rfl) (hS.dn rfl)) hs ho
    exact mk hS hpc hi hst (by decide) rfl rfl rfl rfl (by simp [PcI]) (fun _ _ => rfl) (by simp) (by simp)
      (.inr ⟨_, WEff.of_store h, by simp [sOf, hloc], by simp [Q, hloc]⟩)
  · -- 5: `MOV X3,X2`
    obtain rfl := hz (by decide)
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (exec_mov 5 (.inl rfl) _ (hat (by decide))) hs ho
    exact mk hS hpc hi hst (by decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp) (by simp) (by simp)
      (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 6: `CASAL X3,X1,[X0]`
    obtain rfl := hz (by decide)
    obtain ⟨k, hex⟩ := exec_casal 6 (.inl rfl) _ (hat (by decide)) hdT hS.x0 hS.dt
    simp only [↓reduceIte] at hex
    obtain ⟨tr, old, hst, -, hlw, hcase⟩ := SpinSemShape.spec_rmwo_p _ _ rfl hex hs ho
    have hx := hI (.inl rfl)
    refine mk hS hpc hi hst (by decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp) (by simp)
      (fun _ hl => by simp [hlw hl]) ?_
    rcases hcase with ⟨hop, hm, hp, -⟩ | ⟨new, hop, h⟩
    · have hne : BitVec.setWidth 64 old ≠ u.st.st.1.regs.X3.toBitVec := fun e => by simp [e] at hop
      exact .inl ⟨hm, hp, by simp [sOf]; rw [← hx]; simp [hne]⟩
    · have he : BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec := by
        by_cases e : BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec
        · exact e
        · simp [e] at hop
      simp only [he, ↓reduceIte, Option.some.injEq] at hop
      refine .inr ⟨_, WEff.of_rmw h, by simp [sOf, he, hx], fun _ => ?_⟩
      simp only [← hop, hS.x1 rfl]
  · -- 7: `CMP X3,X2`
    obtain rfl := hz (by decide)
    obtain ⟨fs, hex, hzf⟩ := exec_cmp 7 (.inl rfl) _ (hat (by decide))
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
    refine mk hS hpc hi hst (by decide) rfl rfl rfl rfl (by simp [PcI]) (by simp) (by simp) (by simp)
      (.inl ⟨hm, hp, ?_⟩)
    by_cases e : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec
    · simp [sOf, e, hzf.mpr e]
    · have : ¬ fs.z = true := fun h => e (hzf.mp h)
      simp [sOf, e, this]
  · -- 8: `B.NE push`
    obtain rfl := hz (by decide)
    have hex := exec_bne8 _ (hat (by decide))
    by_cases hzz : u.st.st.1.status.z = true
    · simp only [hzz, ↓reduceIte] at hex
      obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by decide) (by simp [nextP, hzz]) rfl rfl rfl (by simp [PcI]) (by simp) (by simp)
        (by simp) (.inl ⟨hm, hp, by simp [sOf, hzz]⟩)
    · simp only [hzz, Bool.false_eq_true, ↓reduceIte] at hex
      obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by decide) (by simp [nextP, hzz]) rfl rfl rfl (by simp [PcI]) (by simp) (by simp)
        (by simp) (.inl ⟨hm, hp, by simp [sOf, hzz]⟩)
  · -- 9: `B pdone`
    obtain rfl := hz (by decide)
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (exec_b9 _ (hat (by decide))) hs ho
    exact mk hS hpc hi hst (by decide) rfl rfl rfl rfl (by simp [PcI]) (by simp) (by simp) (by simp)
      (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 11: the pusher's end
    obtain rfl := hz (by decide)
    rw [stepOne_end' hS hpc] at hs; cases hs
  · -- 13: `LDAR X2,[X0]`
    have r1 := hnz (by decide)
    obtain ⟨k, hex⟩ := exec_ldar 13 (.inr rfl) _ (hat (by rw [e1 r1]; decide)) hdT hS.x0 hS.dt
    obtain ⟨ts, v, hst, -, hlw, hm, hp, -⟩ := spec_load _ _ hex hs ho
    exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl rfl rfl rfl (by simp [PcI]) (by simp)
      (fun _ hl => by simp [hlw hl]) (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 14: `CBZ X2,popper`
    have r1 := hnz (by decide)
    have hex := exec_cbz14 _ (hat (by rw [e1 r1]; decide))
    by_cases hzz : u.st.st.1.regs.X2.toBitVec = 0#64
    · simp only [hzz, ↓reduceIte] at hex
      obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by rw [p1 r1]; decide) (by simp [nextP, hzz]) rfl rfl rfl (by simp [PcI]) (by simp)
        (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
    · simp only [hzz, ↓reduceIte] at hex
      obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by rw [p1 r1]; decide) (by simp [nextP, hzz]) rfl rfl rfl (by simp [PcI]) (by simp)
        (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 15: `LDR X4,[X2,#8]`
    have r1 := hnz (by decide)
    rcases exec_ldr15 _ (hat (by rw [e1 r1]; decide)) with ⟨v4, hex⟩ | hex
    · obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp)
        (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
    · obtain ⟨l, hex⟩ := access_ok hs ho hex
      obtain ⟨ts, v, hst, -, -, hm, hp, -⟩ := spec_load _ _ hex hs ho
      exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp)
        (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 16: `MOV X3,X2`
    have r1 := hnz (by decide)
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (exec_mov 16 (.inr rfl) _ (hat (by rw [e1 r1]; decide))) hs ho
    exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp) (by simp)
      (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 17: `CASAL X3,X4,[X0]`
    have r1 := hnz (by decide)
    obtain ⟨k, hex⟩ := exec_casal 17 (.inr rfl) _ (hat (by rw [e1 r1]; decide)) hdT hS.x0 hS.dt
    simp only [show (17 : Nat) ≠ 6 by decide, ↓reduceIte] at hex
    obtain ⟨tr, old, hst, -, hlw, hcase⟩ := SpinSemShape.spec_rmwo_p _ _ rfl hex hs ho
    have hx := hI (.inr rfl)
    refine mk hS hpc hi hst (by rw [p1 r1]; decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp) (by simp)
      (fun _ hl => by simp [hlw hl]) ?_
    rcases hcase with ⟨hop, hm, hp, -⟩ | ⟨new, hop, h⟩
    · have hne : BitVec.setWidth 64 old ≠ u.st.st.1.regs.X3.toBitVec := fun e => by simp [e] at hop
      exact .inl ⟨hm, hp, by simp [sOf]; rw [← hx]; simp [hne]⟩
    · have he : BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec := by
        by_cases e : BitVec.setWidth 64 old = u.st.st.1.regs.X3.toBitVec
        · exact e
        · simp [e] at hop
      exact .inr ⟨_, WEff.of_rmw h, by simp [sOf, he, hx], by simp [Q, r1]⟩
  · -- 18: `CMP X3,X2`
    have r1 := hnz (by decide)
    obtain ⟨fs, hex, hzf⟩ := exec_cmp 18 (.inr rfl) _ (hat (by rw [e1 r1]; decide))
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
    refine mk hS hpc hi hst (by rw [p1 r1]; decide) rfl rfl rfl rfl (by simp [PcI]) (by simp) (by simp) (by simp)
      (.inl ⟨hm, hp, ?_⟩)
    by_cases e : u.st.st.1.regs.X3.toBitVec = u.st.st.1.regs.X2.toBitVec
    · simp [sOf, e, hzf.mpr e]
    · have : ¬ fs.z = true := fun h => e (hzf.mp h)
      simp [sOf, e, this]
  · -- 19: `B.NE popper`
    have r1 := hnz (by decide)
    have hex := exec_bne19 _ (hat (by rw [e1 r1]; decide))
    by_cases hzz : u.st.st.1.status.z = true
    · simp only [hzz, ↓reduceIte] at hex
      obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by rw [p1 r1]; decide) (by simp [nextP, hzz]) rfl rfl rfl (by simp [PcI]) (by simp)
        (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf, hzz]⟩)
    · simp only [hzz, Bool.false_eq_true, ↓reduceIte] at hex
      obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ hex hs ho
      exact mk hS hpc hi hst (by rw [p1 r1]; decide) (by simp [nextP, hzz]) rfl rfl rfl (by simp [PcI]) (by simp)
        (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf, hzz]⟩)
  · -- 20: `MOV X10,X2`
    have r1 := hnz (by decide)
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (exec_mov20 _ (hat (by rw [e1 r1]; decide))) hs ho
    exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp) (by simp)
      (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 21: `LDR W11,[X2]`
    have r1 := hnz (by decide)
    obtain ⟨l, hex⟩ := access_ok hs ho (exec_ldr21 _ (hat (by rw [e1 r1]; decide)) (hS.d4 r1 _))
    obtain ⟨ts, v, hst, -, -, hm, hp, -⟩ := spec_load _ _ hex hs ho
    exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl (by simp) (by simp) rfl (by simp [PcI]) (by simp)
      (by simp) (by simp) (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 22: `B qdone`
    have r1 := hnz (by decide)
    obtain ⟨hm, hst, hp, -⟩ := spec_done _ _ (exec_b22 _ (hat (by rw [e1 r1]; decide))) hs ho
    exact mk hS hpc hi hst (by rw [p1 r1]; decide) rfl rfl rfl rfl (by simp [PcI]) (by simp) (by simp) (by simp)
      (.inl ⟨hm, hp, by simp [sOf]⟩)
  · -- 24: the popper's end
    have r1 := hnz (by decide)
    rw [stepOne_end' hS (by rw [hpc, e1 r1])] at hs; cases hs

omit hD hN htn in
/-- **The loads of `top` are reads of `top`** (for memory fairness). -/
theorem step_reads (hpc : PcOK r u.st) (h3 : pos u = 3 ∨ pos u = 13) :
    ∃ ts v ν, TraceEv.read (topL t) ts v ν ∈ o.log := by
  obtain ⟨i, hi, hpc, -⟩ := hpc
  have hi' : i = 3 ∨ i = 13 := by rwa [pos, hpc, posOf_pcT (mem_tPcs hi)] at h3
  have he : i ≠ endP r := by
    unfold endP; split <;> rcases hi' with rfl | rfl <;> first | decide | (simp_all [pcsR])
  obtain ⟨k, hex⟩ := exec_ldar i hi' _ (hS.at hi he hpc) (by rw [hS.decls]; exact hT) hS.x0 hS.dt
  obtain ⟨ts, v, -, -, -, -, -, ν, hl⟩ := spec_load _ _ hex hs ho
  exact ⟨ts, v, ν, hl⟩

end Steps

/-! ## The invariant -/

section Inv

variable {ds : Decls} {t n : BitVec 64} (hT : ds.AgreesAt t 8) (hD : ds.AgreesAt n 4)
  (hN : ds.AgreesAt (n + 8#64) 8) (htn : t ≠ n + 8#64)
include hT hD hN htn

/-- **Every instruction of a thread drops at most one promise**, on any run of
the thread alone. -/
theorem dropBounded {r tid : Nat} {u : Thread isa} (hS : Static ds t n r u.st) (hP : PcOK r u.st) :
    DropBounded Arch.armv8 1 tid u :=
  dropBounded_of_stateInv (fun s => Static ds t n r s ∧ PcOK r s) (fun h hs ho => by
    have q := thread_step hT hD hN htn h.1 hs ho h.2
    refine ⟨⟨q.st, q.pc⟩, ?_⟩
    rcases q.eff with ⟨-, hp, -⟩ | ⟨w, hw, -⟩
    · rw [hp]; omega
    · exact hw.len) ⟨hS, hP⟩

/-- **A certifiable thread's promises are writes `Q` allows.** -/
theorem good_of_certOkN {r tid fuel : Nat} {u : Thread isa} {mem : Memory} (hc : CertOkN Arch.armv8 tid u mem fuel)
    (hS : Static ds t n r u.st) (hP : PcOK r u.st) : ∀ ts ∈ u.prom, ∀ w, mem.get? ts = some w → Q n t r w :=
  TreiberPp.promGood_of_certOkN (fun s => Static ds t n r s ∧ PcOK r s) (Q n t r) (fun h hs ho => by
    have q := thread_step hT hD hN htn h.1 hs ho h.2
    refine ⟨⟨q.st, q.pc⟩, ?_⟩
    rcases q.eff with ⟨hm, hp, -⟩ | ⟨w, hw, -, hq⟩
    · exact .inl ⟨hm, hp⟩
    · exact .inr ⟨w, hw, hq⟩) hc ⟨hS, hP⟩

omit hT hD hN htn

/-- **The per-thread invariant** (role `r`). -/
structure TI (ds : Decls) (t n : BitVec 64) (r fuel : Nat) (u : Thread isa) (mem : Memory) : Prop where
  st : Static ds t n r u.st
  pc : PcOK r u.st
  promLe : ∀ ts ∈ u.prom, ts ≤ mem.last
  plen : u.prom.length ≤ fuel
  good : ∀ ts ∈ u.prom, ∀ w, mem.get? ts = some w → Q n t r w

theorem TI.mono {r fuel : Nat} {u : Thread isa} {mem mem' : Memory} (h : TI ds t n r fuel u mem)
    (hp : mem.Prefix mem') : TI ds t n r fuel u mem' :=
  ⟨h.st, h.pc, fun ts hts => Nat.le_trans (h.promLe ts hts) hp.last_le, h.plen,
    fun ts hts w hw => h.good ts hts w (by rw [← hp.get? (h.promLe ts hts)]; exact hw)⟩

/-- **The invariant**: thread `i` has role `i`. -/
structure Inv (ds : Decls) (t n : BitVec 64) (fuel : Nat) (c : Config isa) : Prop where
  bnd : c.Bnd
  size : c.threads.size = 2
  thr : ∀ (i : Nat) (u : Thread isa), c.threads[i]? = some u → TI ds t n i fuel u c.mem
  cnt : c.mem.cntBelow (topL t) c.mem.last ≤ tsum c fun _ u => S u + c.mem.promAt (topL t) u.prom
  topN : ∀ u, c.threads[0]? = some u → 1 ≤ S u →
    ∃ ts w, c.mem.get? ts = some w ∧ w.loc = topL t ∧ w.val = BitVec.setWidth 128 n

variable {fuel : Nat} {c : Config isa} {tid : Nat} {u : Thread isa}

theorem Inv.build (h : Inv ds t n fuel c) (ht : c.threads[tid]? = some u) {u' : Thread isa}
    {mem' : Memory} (hpre : c.mem.Prefix mem') (hb : (c.withThread tid u' mem').Bnd)
    (hT : TI ds t n tid fuel u' mem')
    (hcnt : mem'.cntBelow (topL t) mem'.last + (S u + c.mem.promAt (topL t) u.prom) ≤
      c.mem.cntBelow (topL t) c.mem.last + (S u' + mem'.promAt (topL t) u'.prom))
    (hN : tid = 0 → 1 ≤ S u' → ∃ ts w, mem'.get? ts = some w ∧ w.loc = topL t ∧ w.val = BitVec.setWidth 128 n) :
    Inv ds t n fuel (c.withThread tid u' mem') := by
  refine ⟨hb, by rw [withThread_size]; exact h.size, fun i v hv => ?_, ?_, fun v hv h1 => ?_⟩
  · rcases SpinStep.wt_get ht hv with ⟨rfl, rfl⟩ | ⟨-, hv⟩
    · exact hT
    · exact (h.thr i v hv).mono hpre
  · have e := tsum_withThread_add (t' := u') (mem' := mem')
      (F := fun (_ : Nat) (v : Thread isa) => S v + c.mem.promAt (topL t) v.prom)
      (F' := fun (_ : Nat) (v : Thread isa) => S v + mem'.promAt (topL t) v.prom) ht fun i v _ hv => by
        simp only [promAt_prefix hpre (h.thr i v hv).promLe]
    have := h.cnt
    show mem'.cntBelow (topL t) mem'.last ≤
      tsum (c.withThread tid u' mem') fun _ v => S v + mem'.promAt (topL t) v.prom
    omega
  · rcases SpinStep.wt_get ht hv with ⟨rfl, rfl⟩ | ⟨-, hv⟩
    · exact hN rfl h1
    · obtain ⟨ts, w, hw, h2⟩ := h.topN v hv h1
      exact ⟨ts, w, show mem'.get? ts = some w by rw [hpre.get? (c.mem.last_le_of_get?_eq_some hw)]; exact hw, h2⟩

include hT hD hN htn in
/-- **A semantic step keeps the invariant.** -/
theorem Inv.step (h : Inv ds t n fuel c) (ht : c.threads[tid]? = some u) {c' : Config isa}
    (hst : StepSem Arch.armv8 fuel tid c c') : Inv ds t n fuel c' := by
  have hb := h.bnd.semStep hst
  have hTI := h.thr tid u ht
  rcases hst with ⟨t1, outs, o, ht1, hs, ho, hc, rfl⟩ | ⟨t1, w, ht1, -, hc, rfl⟩
  · rw [ht] at ht1; cases ht1
    have q := thread_step hT hD hN htn hTI.st hs ho hTI.pc
    have hpre : c.mem.Prefix o.mem := (stepOne_dord _ hs ho).2.2.1
    have hplen : o.thread.prom.length ≤ fuel := by
      have := prom_le_of_certOkN (dropBounded hT hD hN htn q.st q.pc) hc; omega
    have hgood := good_of_certOkN hT hD hN htn hc q.st q.pc
    rcases q.eff with ⟨hm, hp, hS⟩ | ⟨w, hw, hS, hq⟩
    · refine h.build ht hpre hb ⟨q.st, q.pc, by rw [hp, hm]; exact hTI.promLe, hplen, hgood⟩ ?_ fun e h1 => ?_
      · rw [hm, hp, hS]; omega
      · subst e; rw [hm]; exact h.topN u ht (hS ▸ h1)
    · obtain ⟨e, hle⟩ := count_weff (l := topL t) hTI.promLe hw
      refine h.build ht hpre hb ⟨q.st, q.pc, hle, hplen, hgood⟩ ?_ fun e0 h1 => ?_
      · by_cases hl : w.loc = topL t <;> simp only [hl, ↓reduceIte] at hS e <;> omega
      · subst e0
        by_cases h0 : 1 ≤ S u
        · obtain ⟨ts, w', hw', h2⟩ := h.topN u ht h0
          exact ⟨ts, w', by rw [hpre.get? (c.mem.last_le_of_get?_eq_some hw')]; exact hw', h2⟩
        · have hl : w.loc = topL t := by
            by_cases hl : w.loc = topL t
            · exact hl
            · simp only [hl, ↓reduceIte] at hS; omega
          have hv : w.val = BitVec.setWidth 128 n := by simp only [Q, ↓reduceIte] at hq; exact hq hl
          rcases hw with ⟨hm, -⟩ | ⟨ts, -, hts, hm, -⟩
          · exact ⟨c.mem.last + 1, w, by rw [hm]; exact Memory.get?_append_last _ _, hl, hv⟩
          · exact ⟨ts, w, by rw [hm]; exact hts, hl, hv⟩
  · rw [ht] at ht1; cases ht1
    have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append _ _
    have hplen : (promThread u c.mem w).prom.length ≤ fuel := by
      have := prom_le_of_certOkN (dropBounded hT hD hN htn (u := promThread u c.mem w) (tid := tid) hTI.st hTI.pc) hc
      omega
    have hlast : (c.mem.append w).1.last = c.mem.last + 1 := by simp [Memory.append, Memory.last]
    refine h.build ht hpre hb ⟨hTI.st, hTI.pc, fun ts hts => ?_, hplen,
      good_of_certOkN hT hD hN htn hc hTI.st hTI.pc⟩ ?_ fun e h1 => ?_
    · rw [hlast]
      rcases List.mem_append.mp hts with hts | hts
      · exact Nat.le_succ_of_le (hTI.promLe ts hts)
      · rw [List.mem_singleton] at hts; rw [hts]; exact Nat.le_refl _
    · show _ + (S u + _) ≤ _ + (S u + (c.mem.append w).1.promAt (topL t) (u.prom ++ [(c.mem.append w).2]))
      rw [cntBelow_append, promAt_promise w hTI.promLe]
      omega
    · subst e
      obtain ⟨ts, w', hw', h2⟩ := h.topN u ht h1
      exact ⟨ts, w', by rw [hpre.get? (c.mem.last_le_of_get?_eq_some hw')]; exact hw', h2⟩

/-- **The invariant at the start**: the pusher at `1`, the popper at `13`. -/
theorem Inv.init {sP sQ : isa.State} {initMem : List (Loc × Val)} (hP : Static ds t n 0 sP)
    (hpP : sP.st.2 = pcT 1) (hQ : Static ds t n 1 sQ) (hpQ : sQ.st.2 = pcT 13) :
    Inv ds t n fuel (Config.init [sP, sQ] initMem) := by
  refine ⟨Config.init_bnd _ _, rfl, fun i v hv => ?_, by
    show _ ≤ _
    have : (Config.init [sP, sQ] initMem : Config isa).mem.last = 0 := rfl
    rw [this]; exact Nat.zero_le _, fun v hv h1 => ?_⟩
  · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hv
    obtain ⟨s, hm, rfl⟩ := hv
    rcases i with _ | _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
      exact ⟨hP, ⟨1, by decide, hpP, by simp [PcI]⟩, by simp [Thread.init], by simp [Thread.init],
        by simp [Thread.init]⟩
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
      exact ⟨hQ, ⟨13, by decide, hpQ, by simp [PcI]⟩, by simp [Thread.init], by simp [Thread.init],
        by simp [Thread.init]⟩
    · simp at hm
  · simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hv
    obtain ⟨s, hm, rfl⟩ := hv
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
    simp only [S, pos, Thread.init] at h1
    rw [hpP, posOf_pcT (show 1 ∈ tPcs by decide)] at h1
    simp [sOf] at h1

end Inv

end Kraken.Promising.Live.TreiberPpA64
