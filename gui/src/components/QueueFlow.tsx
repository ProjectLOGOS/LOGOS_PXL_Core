import { Sankey, Tooltip, ResponsiveContainer } from "recharts";
export default function QueueFlow(){
  const nodes=[{name:"Ingress"},{name:"ARCHON"},{name:"RabbitMQ"},{name:"TELOS"},{name:"TETRAGNOS"},{name:"THONOC"}];
  const links=[{source:0,target:1,value:20},{source:1,target:2,value:20},{source:2,target:3,value:7},{source:2,target:4,value:8},{source:2,target:5,value:5}];
  return <div style={{height:220}}><ResponsiveContainer><Sankey width={600} height={220} data={{nodes,links}} nodePadding={30}><Tooltip/></Sankey></ResponsiveContainer></div>;
}