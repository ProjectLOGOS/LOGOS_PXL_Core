$body = @{ task_type="predict_outcomes"; payload=@{x=1}; provenance=@{src="smoke"} } | ConvertTo-Json
Invoke-RestMethod -Method POST -Uri "http://127.0.0.1:8075/dispatch" -ContentType "application/json" -Body $body | ConvertTo-Json -Compress
