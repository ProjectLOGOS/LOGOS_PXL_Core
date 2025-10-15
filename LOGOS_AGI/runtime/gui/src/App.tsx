import { BrowserRouter, Routes, Route, Link } from "react-router-dom";
import StatusBar from "./components/StatusBar";
import ProofConsole from "./components/ProofConsole";
import OverlayInspector from "./components/OverlayInspector";
import HealthDashboard from "./components/HealthDashboard";
import ProvenanceBanner from "./components/ProvenanceBanner";

function Home(){
  return (
    <div style={{padding:16}}>
      <h2>LOGOS PXL Core - Production GUI</h2>
      <p>Coq-verified proof and overlay services for LOGOS AGI</p>
      <div style={{display: 'grid', gridTemplateColumns: 'repeat(auto-fit, minmax(200px, 1fr))', gap: '16px', marginTop: '24px'}}>
        <Link to="/proofs" style={{padding: '16px', border: '1px solid #ccc', borderRadius: '8px', textDecoration: 'none', color: 'inherit'}}>
          <h3>Proof Console</h3>
          <p>Submit goals and monitor proof progress</p>
        </Link>
        <Link to="/overlays" style={{padding: '16px', border: '1px solid #ccc', borderRadius: '8px', textDecoration: 'none', color: 'inherit'}}>
          <h3>Overlay Inspector</h3>
          <p>Inspect Chrono and V4 adapter operations</p>
        </Link>
        <Link to="/health" style={{padding: '16px', border: '1px solid #ccc', borderRadius: '8px', textDecoration: 'none', color: 'inherit'}}>
          <h3>Health & Provenance</h3>
          <p>System health and cryptographic provenance</p>
        </Link>
      </div>
    </div>
  );
}

export default function App(){
  return (
    <BrowserRouter>
      <ProvenanceBanner />
      <StatusBar/>
      <nav style={{padding:8, borderBottom:"1px solid #eee"}}>
        <Link to="/" style={{marginRight: '16px'}}>Home</Link>
        <Link to="/proofs" style={{marginRight: '16px'}}>Proof Console</Link>
        <Link to="/overlays" style={{marginRight: '16px'}}>Overlay Inspector</Link>
        <Link to="/health">Health & Provenance</Link>
      </nav>
      <Routes>
        <Route path="/" element={<Home/>}/>
        <Route path="/proofs" element={<ProofConsole/>}/>
        <Route path="/overlays" element={<OverlayInspector/>}/>
        <Route path="/health" element={<HealthDashboard/>}/>
      </Routes>
    </BrowserRouter>
  );
}
