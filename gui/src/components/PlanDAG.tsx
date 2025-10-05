import cytoscape from "cytoscape";
import { useEffect, useRef } from "react";
export default function PlanDAG(){
  const ref = useRef<HTMLDivElement>(null);
  useEffect(()=>{
    if(!ref.current) return;
    const cy = cytoscape({
      container: ref.current,
      elements: [
        { data:{ id:"s1", label:"step_prepare", box:true } },
        { data:{ id:"s2", label:"step_commit", box:true } },
        { data:{ id:"e1", source:"s1", target:"s2", diamond:true } }
      ],
      style: [
        { selector:"node", style:{ "label":"data(label)","background-color":"#bbb","text-valign":"center" } },
        { selector:"edge", style:{ "curve-style":"bezier","width":2 } },
        { selector:'node[box = "true"]', style:{ "border-width":3,"border-color":"#22aa22" } },
        { selector:'edge[diamond = "true"]', style:{ "line-color":"#22aa22" } }
      ],
      layout:{ name:"grid", rows:1 }
    });
    return ()=>cy.destroy();
  },[]);
  return <div style={{height:260,border:"1px solid #eee",borderRadius:8}} ref={ref} />;
}