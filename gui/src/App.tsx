import { BrowserRouter, Routes, Route, Link } from "react-router-dom";
import StatusBar from "./components/StatusBar";
import ProofTimeline from "./components/ProofTimeline";
import PlanDAG from "./components/PlanDAG";
import QueueFlow from "./components/QueueFlow";

function Home(){
  return (
    <div style={{padding:16}}>
      <h2>LOGOS Control Plane</h2>
      <ProofTimeline/>
      <h3>Plan Inspector</h3>
      <PlanDAG/>
      <h3>Flow</h3>
      <QueueFlow/>
    </div>
  );
}

export default function App(){
  return (
    <BrowserRouter>
      <StatusBar/>
      <nav style={{padding:8, borderBottom:"1px solid #eee"}}>
        <Link to="/">Home</Link>
      </nav>
      <Routes>
        <Route path="/" element={<Home/>}/>
      </Routes>
    </BrowserRouter>
  );
}
