$dest = 'C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\third_party\logos_agi_v4_local'
$root = 'C:\Users\proje\OneDrive\Desktop\LOGOS SYSTEM\v3'

robocopy "$root" "$dest" /MIR /XD .git node_modules _build _opam target dist build out .venv __pycache__ .vite .next `
  /XF *.vo *.glob *.o *.cm* *.obj *.exe *.dll *.pdb