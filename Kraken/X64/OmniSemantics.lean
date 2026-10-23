/-
Omnisemantics for x64.
-/

import Kraken.Attribute
import Kraken.OmniSemantics
import Kraken.X64.Semantics

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .syscall .. => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post
  -- The ordered access effects are emitted only for an unmapped address, a
  -- fault in the sequential model like `nonmem_*`; a fence is a skip.
  | .sync_load .. => False
  | .sync_store .. => False
  | .rmw .. => False
  | .fence _ cont => (cont ()).All post
  -- Vector accesses: the checks pass through, the unmapped accesses fault.
  | .require_read_access_avx _ _ _ cont => (cont ()).All post
  | .require_write_access_avx _ _ _ cont => (cont ()).All post
  | .nonmem_load_avx .. => False
  | .nonmem_store_avx .. => False
  | .rmw16 .. => False

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post
