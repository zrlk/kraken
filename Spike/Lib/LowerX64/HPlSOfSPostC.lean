/-
**The marshalling block's states placed after the setup call** (x86-64,
option (b)): the `hPlS` premise of the `h0` wrappers with a setup block
(`Spike/Lib/LowerX64/RtMainXR.lean`) from the setup call's post `SPostC`
(`Spike/Lib/LowerX64/PlacedSPostC.lean`). At each state of the marshalling
block from `mainS0R`, the continuation of the setup call is placed: before
the loads every result register still holds its word; from the loads on,
every word is in its slot (the loads overwrite argument registers, some
of them result registers, but no slot). `me`'s word is in the TCB slot
`-16` throughout.

- `marshal_take`: the prefix runs of the marshalling block: the offsets
  kept, the slots the stores' so far, the registers kept before the loads;
- `hPlS_ofSPostC`: `Placed` and `PlacedS` at every state of the
  marshalling block, from `SPostC` at the result type `ty` with its words
  as many as the block's (`valWords ty = some sw`), and `me`'s word
  represented by the TCB;
- `hPl_setupArgs`: `PlacedS` at `main`'s entry, at every state agreeing
  with the entry registers on the six argument registers, from `SetupArgs`
  at `SPostC` (the words in `argXs[0]`…`argXs[sw-1]`, `me`'s in
  `argXs[sw]`).
-/
import Spike.Lib.LowerX64.PlacedSPostC
import Spike.Lib.Rt.X64MainS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (WordPlace WordPlaceRep Place placeVal ValRep)
open Scc.Sem.X64 (machine kernel)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Rt (SetupCode retXs argXs swOff mshSt mshLd marshal marshal_eq xLd xLdRegs arun_cat arun_xLds
  mshSt_off mshLd_reg swOff_toInt mainS0R oU SetupArgs)
open Spike.Lib.X64.Flow.Ret0 (MainG)
open Spike.Lib.X64Consumer

/-- **The marshalling block's prefix runs** from `oU Z`: the offsets kept,
the slots those of the stores run so far (`xStSlots` at the first `k`
stores; the loads store nothing), the registers kept up to the loads. -/
theorem marshal_take (lab : Label → Int64) {sw k : Nat} (fn : Label) (pc : Int64) (Z : Int64) (σ : AS)
    (hk : k < (marshal sw fn).length) :
    (arun lab ((marshal sw fn).take k) ⟨pc, oU Z, σ⟩).so = oU Z ∧
      (arun lab ((marshal sw fn).take k) ⟨pc, oU Z, σ⟩).σ.slot = xStSlots σ.regs ((mshSt sw).take k) σ.slot ∧
      (k ≤ sw → (arun lab ((marshal sw fn).take k) ⟨pc, oU Z, σ⟩).σ.regs = σ.regs) := by
  have hlS : ((mshSt sw).map xSt).length = sw := by simp [mshSt]
  have hlL : ((mshLd sw).map xLd).length = sw + 1 := by simp [mshLd]
  rw [marshal_eq, List.append_assoc]
  rw [marshal_eq, List.length_append, List.length_append, hlS, hlL] at hk
  by_cases hks : k ≤ sw
  · rw [List.take_append_of_le_length (by rw [hlS]; exact hks), ← List.map_take,
      arun_xSts _ _ _ _ (Spike.Lib.X64.Rt.oU_rbp _)]
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · have hcb : (callB fn).length = 1 := rfl
    have hle : k - sw ≤ ((mshLd sw).map xLd).length := by rw [hlL]; rw [hcb] at hk; omega
    rw [List.take_append, List.take_of_length_le (by rw [hlS]; omega), hlS,
      List.take_append_of_le_length hle,
      arun_cat, arun_xSts _ _ _ _ (Spike.Lib.X64.Rt.oU_rbp _), ← List.map_take,
      arun_xLds _ _ _ _ (Spike.Lib.X64.Rt.oU_rbp _)
        (fun p hp => Spike.Lib.X64.Rt.oU_kill _ (mshLd_reg (List.mem_of_mem_take hp)).2)]
    refine ⟨rfl, ?_, fun h => absurd h hks⟩
    show xStSlots σ.regs (mshSt sw) σ.slot = _
    rw [List.take_of_length_le (by simp [mshSt] <;> omega)]

/-- The stores' slots are distinct. -/
theorem mshSt_slots_nodup {sw : Nat} (hsw : sw ≤ 5) : ((mshSt sw).map fun p => -8 + p.2.1.toInt).Nodup := by
  have e : ((mshSt sw).map fun p => -8 + p.2.1.toInt) = (List.range sw).map fun i : Nat => -24 - 8 * (i : Int) := by
    simp only [mshSt, List.map_map]
    exact List.map_congr_left fun i hi => by
      show -8 + (swOff i).toInt = _
      rw [swOff_toInt i (by have := List.mem_range.1 hi; omega)]; omega
  rw [e]
  exact List.Pairwise.map _
    (fun a b hab (h : -24 - 8 * (a : Int) = -24 - 8 * (b : Int)) => hab (by omega)) List.nodup_range

/-- A target place's value at a frame slot: its cell (`Abs.slot`). -/
theorem placeVal_slot {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) {k : Int} (hk : R.Off k)
    (s : State) (hs : s.st.1 = m) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some (σ.slot k).toNat := by
  obtain ⟨j, hj, hjv⟩ := hA.slot k hk
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, Scc.Sem.X64.privLoad, hs, hj]
  simp [hjv]

/-- A target place's value at a register: the register's. -/
theorem placeVal_reg (s : State) (r : Reg64) :
    placeVal (machine (kernel 1)) s (.reg (.r r)) = some (s.st.1.regs.get64 r).toNat := rfl

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The marshalling block's states are placed** (`hPlS`): from
`mainS0R` at the setup call's post `SPostC` at the result type `ty`, whose
words are as many as the block's (`hw`, `hs`), with the stores' slots and
the TCB slot `-16` in the region (`hOff`) and every word of the caller's
environment represented by the TCB `x0` (`hme`), every state of the
marshalling block has the continuation placed, with no suspended frame. -/
theorem hPlS_ofSPostC {Λ : Scc.Sem.Layout} {lbl : Lbl} {p : Prog} {ty : Ty} (lab : Label → Int64)
    {sc : SetupCode} {g : MainG} {x0 : BitVec 64} (hsw : sc.sw ≤ 5) (hs : Scc.Lower.simpleTy ty = true)
    (hw : Scc.Obj.valWords ty = some sc.sw)
    (hOff : R.Off (-16) ∧ ∀ j < sc.sw, R.Off (-24 - 8 * (j : Int)))
    (hme : ∀ y t ws, TermRun.lookupE g.c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat) :
    BlkW (fun s c => Placed Λ lbl s c ∧ Spike.Lib.X64ConsumerS.PlacedS Λ lbl s c []) (fun _ _ => False)
      exe endPc R F (mainS0R lab sc (SPostC p lbl ty g.c0) g x0) (marshal sc.sw sc.fn) := by
  intro s σ c _ _ _ _ _ _ hJ k hk m hAk _
  obtain ⟨⟨hPost, -, -, hx0⟩, -⟩ := hJ
  obtain ⟨ops, hn, hcnt, hP⟩ := hPost.placedP
  have hlen : ops.length = sc.sw := hcnt hs _ hw
  obtain ⟨hso, hsl, hrg⟩ := marshal_take (_root_.Executable.labels exe).label sc.fn
    (mainS0R lab sc (SPostC p lbl ty g.c0) g x0).pc sc.Z σ hk
  have hAk' := hAk
  rw [show (mainS0R lab sc (SPostC p lbl ty g.c0) g x0).o = oU sc.Z from rfl, hso] at hAk'
  obtain ⟨σk, hσk⟩ : ∃ σk, σk = (arun (_root_.Executable.labels exe).label ((marshal sc.sw sc.fn).take k)
    ⟨(mainS0R lab sc (SPostC p lbl ty g.c0) g x0).pc, oU sc.Z, σ⟩).σ := ⟨_, rfl⟩
  rw [← hσk] at hAk'
  have hrr : ∀ j (hj : j < Scc.Emit.X64.retRegs.length), Scc.Emit.X64.retRegs[j] = retXs.getD j .rax :=
    fun j hj => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by exact hj)]; rfl
  -- the TCB slot holds `x0` at every prefix
  have hT : σk.slot (-16) = x0 := by
    rw [hσk, hsl, Spike.Lib.X64.Rt.xStSlots_of_not_mem _ _ _ fun q hq => ?_]
    · exact hx0
    · obtain ⟨i, -, -, e⟩ := mshSt_off hsw (List.mem_of_mem_take hq)
      rw [e]; omega
  let s' : State := { s with st := (m, (mainS0R lab sc (SPostC p lbl ty g.c0) g x0).pc +
    Int64.ofNat (cellOff (marshal sc.sw sc.fn) k)) }
  have hme' : ∀ y t ws, TermRun.lookupE g.c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ∃ wp, OffImm lbl s' ws[k] wp := by
    unfold OffImm
    intro y t ws hl i hi
    refine ⟨.one (.slot (R.addr (-16)).toNat), ⟨fun n h => (by cases h), ?_⟩⟩
    show ∃ v, placeVal (machine (kernel 1)) s' (.slot (R.addr (-16)).toNat) = some v ∧ ValRep lbl ws[i].val v
    exact ⟨x0.toNat, by rw [placeVal_slot hAk' hOff.1 s' rfl, hT], hme y t ws hl i hi⟩
  -- the result words' places
  let ρ : Nat → Place (machine (kernel 1)).I.RegId := fun j =>
    if k ≤ sc.sw then .reg (.r (retXs.getD j .rax)) else .slot (R.addr (-24 - 8 * (j : Int))).toNat
  have hρ : ∀ j (_hj : j < ops.length) (hr : j < Scc.Emit.X64.retRegs.length),
      placeVal (machine (kernel 1)) s' (ρ j) = some (σ.regs.get64 Scc.Emit.X64.retRegs[j]).toNat := by
    intro j hj hr
    rw [hrr j hr]
    by_cases hks : k ≤ sc.sw
    · simp only [ρ, hks, ite_true]
      rw [placeVal_reg]
      show some (m.regs.get64 _).toNat = _
      rw [hAk'.regs, hσk, hrg hks]
    · simp only [ρ, hks, ite_false]
      have hj' : j < sc.sw := hlen ▸ hj
      rw [placeVal_slot hAk' (hOff.2 j hj') s' rfl, hσk, hsl, List.take_of_length_le (by simp [mshSt]; omega)]
      have hm : (retXs.getD j .rax, swOff j, 4) ∈ mshSt sc.sw := Spike.Lib.X64.Rt.mem_mshSt hj'
      have e : -24 - 8 * (j : Int) = -8 + (retXs.getD j .rax, swOff j, 4).2.1.toInt := by
        show _ = -8 + (swOff j).toInt
        rw [swOff_toInt j (by omega)]; omega
      rw [e, Spike.Lib.X64.Rt.xStSlots_get _ _ _ (mshSt_slots_nodup hsw) hm]
  have hPl := hP Λ s' ρ hρ hme'
  exact ⟨⟨hPl, Spike.Lib.X64ConsumerS.PlacedS.ofNil hPl⟩, fun _ h => h⟩

/-- **The continuation placed at `main`'s entry** (`hpro_main`'s `hPl`):
at registers `regs` with `SetupArgs` at the setup call's post `SPostC` at
the result type `ty` of `sw ≤ 5` words (`hs`, `hw`), every state agreeing
with `regs` on the six argument registers has the continuation placed with
no suspended frame: the words in `argXs[0]`…`argXs[sw-1]` (`SPostC.placedP`,
the setup's result registers `retXs` moved there), every word of the
caller's environment represented by the TCB `x0` (`hme`) in `argXs[sw]`. -/
theorem hPl_setupArgs {p : Prog} {lbl : Lbl} {ty : Ty} {c0 : Ctl} {sw : Nat} {x0 : BitVec 64}
    (hs : Scc.Lower.simpleTy ty = true) (hw : Scc.Obj.valWords ty = some sw) (hsw : sw ≤ 5)
    (hme : ∀ y t ws, TermRun.lookupE c0.env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val x0.toNat)
    (Λ : Scc.Sem.Layout) :
    ∀ c (regs : Reg64s), SetupArgs (SPostC p lbl ty c0) sw x0 c regs → ∀ s : State,
      (∀ i < 6, s.st.1.regs.get64 (argXs.getD i .rdi) = regs.get64 (argXs.getD i .rdi)) →
      Spike.Lib.X64ConsumerS.PlacedS Λ lbl s c [] := by
  rintro c regs ⟨rs, hP, hrs, hx⟩ s hag
  obtain ⟨ops, -, hcnt, hPl⟩ := hP.placedP
  have hlen : ops.length = sw := hcnt hs _ hw
  have hpl := hPl Λ s (fun j => .reg (.r (argXs.getD j .rdi))) (fun j hj hr => by
      have hjs : j < sw := hlen ▸ hj
      rw [placeVal_reg, hag j (by omega), hrs j hjs]
      congr 3
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by exact hr)]; rfl)
    (fun y t ws hl k hk => ⟨.one (.reg (.r (argXs.getD sw .rdi))), ⟨fun n h => (by cases h),
      ⟨x0.toNat, by rw [placeVal_reg, hag sw (by omega), hx], hme y t ws hl k hk⟩⟩⟩)
  exact Spike.Lib.X64ConsumerS.PlacedS.ofNil hpl

/-- info: 'Spike.Lib.LowerX64.marshal_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms marshal_take

/-- info: 'Spike.Lib.LowerX64.hPlS_ofSPostC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hPlS_ofSPostC

/-- info: 'Spike.Lib.LowerX64.hPl_setupArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hPl_setupArgs

end Spike.Lib.LowerX64
