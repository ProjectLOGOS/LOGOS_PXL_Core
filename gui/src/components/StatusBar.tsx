import { useEffect } from "react";
import { api } from "../lib/api";
import { useStore } from "../lib/state";

export default function StatusBar(){
  const {status,setStatus}=useStore();
  useEffect(()=>{ api.status().then(setStatus).catch(()=>{}); },[]);
  return (
    <div style={{display:"flex",gap:16,padding:8,borderBottom:"1px solid #eee"}}>
      <div><b>Kernel:</b> {status.kernel_hash_expected??"…"}</div>
      <div><b>Prover:</b> {status.prover_url??"…"}</div>
      <div><b>Audit:</b> {status.audit_path??"…"}</div>
    </div>
  );
}