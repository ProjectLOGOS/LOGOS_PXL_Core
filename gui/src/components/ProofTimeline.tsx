import { useEffect, useState } from "react";
import { LineChart, Line, XAxis, YAxis, Tooltip, ResponsiveContainer } from "recharts";

export default function ProofTimeline(){
  const [data,setData]=useState<{ts:number,lat:number}[]>([]);
  useEffect(()=>{
    // TODO: swap with real /proofs feed; placeholder data
    const now=Date.now(); setData(Array.from({length:30},(_,i)=>({ts:now-30000+1000*i,lat:5+Math.random()*50})));
  },[]);
  return (
    <div style={{height:200}}>
      <ResponsiveContainer>
        <LineChart data={data}>
          <XAxis dataKey="ts" tickFormatter={(t)=>new Date(t).toLocaleTimeString()} />
          <YAxis />
          <Tooltip />
          <Line type="monotone" dataKey="lat" dot={false} />
        </LineChart>
      </ResponsiveContainer>
    </div>
  );
}