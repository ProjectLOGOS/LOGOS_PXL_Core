import json
import sys

src, out = sys.argv[1], sys.argv[2]
with open(src,encoding="utf-8") as f: data=json.load(f)

props = data.get("properties",{})
gc = data.get("group_classifications",{})

# Remap: Will -> Volitional
if "Will" in props:
    props["Will"]["group"] = "Volitional"

# Ensure group_classifications reflect the move
# Remove Will from Causal list if present
causal = gc.get("Causal",{}).get("properties",[])
if "Will" in causal:
    causal = [x for x in causal if x != "Will"]
    gc["Causal"]["properties"] = causal

# Add Will to Volitional list
vol = gc.setdefault("Volitional", {"description":"Attributes related to will, choice, and freedom",
                                   "properties":[], "characteristic_goodness_weight":"high"})
if "Will" not in vol["properties"]:
    vol["properties"].append("Will")

# Keep Immanence under Spatial (no change)

with open(out,"w",encoding="utf-8") as f: json.dump(data,f,indent=2)
print("[OK] Remapped Will→Volitional in", out)
