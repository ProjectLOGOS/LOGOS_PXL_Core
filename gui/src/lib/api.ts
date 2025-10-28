import axios from "axios";
const ARCHON = import.meta.env.VITE_ARCHON as string;
const LOGOS  = import.meta.env.VITE_LOGOS  as string;

export const api = {
  status: async () => (await axios.get(`${LOGOS}/gui/status`)).data,
  health: async () => ({
    archon: (await axios.get(`${ARCHON}/health`)).data,
    logos:  (await axios.get(`${LOGOS}/health`)).data
  }),
  dispatch: async (task_type: string, payload: any, provenance: any={src:"gui"}) =>
    (await axios.post(`${ARCHON}/dispatch`, { task_type, payload, provenance })).data
};