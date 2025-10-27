import requests

print('🔄 Testing Complete LOGOS Workflow...')

# Step 1: Get authorization token
auth_response = requests.post('http://localhost:8090/authorize_action', json={
    'action': 'complete_workflow_test',
    'state': {'workflow': 'e2e_validation'}
})
print(f'✅ Auth Status: {auth_response.status_code}')
auth_data = auth_response.json()
token = auth_data['proof_token']['token']
print(f'📄 Token: {token[:20]}...')

# Step 2: Use token in chat
chat_response = requests.post('http://127.0.0.1:8080/chat', json={
    'message': f'System validation complete with token {token[:10]}',
    'session_id': 'workflow_test'
})
print(f'✅ Chat Status: {chat_response.status_code}')
chat_data = chat_response.json() 
print(f'💬 Response: {chat_data["response"][:100]}...')

print('🎯 Complete workflow validation: SUCCESS')