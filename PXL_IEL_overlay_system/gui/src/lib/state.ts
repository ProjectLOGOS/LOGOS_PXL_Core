import { create } from "zustand";
type Status = { kernel_hash_expected?:string; prover_url?:string; audit_path?:string };
export const useStore = create<{status:Status, setStatus:(s:Status)=>void}>(set => ({
  status:{}, setStatus:(s)=>set({status:s})
}));