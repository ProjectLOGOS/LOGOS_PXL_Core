"""
LOGOS PXL Core - RBAC Authentication System
Role-based access control for GUI and services
"""
import jwt
import hashlib
import time
from typing import Dict, Any, Optional, List
from enum import Enum

class UserRole(Enum):
    VIEWER = "viewer"        # Read-only access to dashboards
    OPERATOR = "operator"    # Can trigger tests and view detailed logs  
    SPEC_AUTHOR = "spec_author"  # Can modify specifications and policies
    AUDITOR = "auditor"      # Full audit trail access and verification
    ADMIN = "admin"          # Full system administration

class RBACManager:
    """Role-based access control manager"""
    
    def __init__(self, secret_key: str = "pilot_secret_change_in_production"):
        self.secret_key = secret_key
        self.role_permissions = {
            UserRole.VIEWER: {
                "read_dashboard", "read_health", "read_status"
            },
            UserRole.OPERATOR: {
                "read_dashboard", "read_health", "read_status", 
                "test_authorization", "test_crawl", "read_logs"
            },
            UserRole.SPEC_AUTHOR: {
                "read_dashboard", "read_health", "read_status",
                "test_authorization", "test_crawl", "read_logs",
                "modify_specs", "update_policies"
            },
            UserRole.AUDITOR: {
                "read_dashboard", "read_health", "read_status",
                "read_logs", "read_audit", "verify_audit", "export_audit"
            },
            UserRole.ADMIN: {
                "read_dashboard", "read_health", "read_status",
                "test_authorization", "test_crawl", "read_logs",
                "modify_specs", "update_policies", "read_audit",
                "verify_audit", "export_audit", "manage_users",
                "system_admin", "emergency_override"
            }
        }
        
        # Pilot users (in production, use proper user management)
        self.pilot_users = {
            "pilot_viewer": {"role": UserRole.VIEWER, "password_hash": self._hash_password("viewer123")},
            "pilot_operator": {"role": UserRole.OPERATOR, "password_hash": self._hash_password("operator123")},
            "pilot_admin": {"role": UserRole.ADMIN, "password_hash": self._hash_password("admin123")},
            "pilot_auditor": {"role": UserRole.AUDITOR, "password_hash": self._hash_password("auditor123")}
        }
    
    def _hash_password(self, password: str) -> str:
        """Hash password with salt"""
        salt = "logos_pilot_salt"  # In production, use random salt per user
        return hashlib.sha256((password + salt).encode()).hexdigest()
    
    def authenticate(self, username: str, password: str) -> Optional[str]:
        """Authenticate user and return JWT token"""
        if username not in self.pilot_users:
            return None
        
        user = self.pilot_users[username]
        password_hash = self._hash_password(password)
        
        if password_hash != user["password_hash"]:
            return None
        
        # Generate JWT token
        payload = {
            "username": username,
            "role": user["role"].value,
            "issued_at": int(time.time()),
            "expires_at": int(time.time()) + 86400  # 24 hours
        }
        
        token = jwt.encode(payload, self.secret_key, algorithm="HS256")
        return token
    
    def verify_token(self, token: str) -> Optional[Dict[str, Any]]:
        """Verify JWT token and return user info"""
        try:
            payload = jwt.decode(token, self.secret_key, algorithms=["HS256"])
            
            # Check expiration
            if payload["expires_at"] < int(time.time()):
                return None
            
            return payload
        except jwt.InvalidTokenError:
            return None
    
    def check_permission(self, token: str, required_permission: str) -> bool:
        """Check if user has required permission"""
        user_info = self.verify_token(token)
        if not user_info:
            return False
        
        user_role = UserRole(user_info["role"])
        user_permissions = self.role_permissions.get(user_role, set())
        
        return required_permission in user_permissions
    
    def get_user_permissions(self, token: str) -> List[str]:
        """Get all permissions for user"""
        user_info = self.verify_token(token)
        if not user_info:
            return []
        
        user_role = UserRole(user_info["role"])
        return list(self.role_permissions.get(user_role, set()))
    
    def create_session_info(self, token: str) -> Dict[str, Any]:
        """Create session information for frontend"""
        user_info = self.verify_token(token)
        if not user_info:
            return {"authenticated": False}
        
        permissions = self.get_user_permissions(token)
        
        return {
            "authenticated": True,
            "username": user_info["username"],
            "role": user_info["role"],
            "permissions": permissions,
            "expires_at": user_info["expires_at"]
        }

# Decorator for protecting endpoints
def require_permission(permission: str):
    """Decorator to require specific permission for endpoint access"""
    def decorator(func):
        def wrapper(*args, **kwargs):
            # In a real FastAPI app, extract token from request headers
            # For pilot, we'll integrate this with the GUI server
            return func(*args, **kwargs)
        return wrapper
    return decorator

# Global RBAC manager
rbac = RBACManager()

if __name__ == "__main__":
    print("🔐 LOGOS RBAC System - Pilot Users")
    print("=" * 40)
    
    # Test authentication
    for username in rbac.pilot_users.keys():
        role = rbac.pilot_users[username]["role"].value
        password = {
            "pilot_viewer": "viewer123",
            "pilot_operator": "operator123", 
            "pilot_admin": "admin123",
            "pilot_auditor": "auditor123"
        }[username]
        
        token = rbac.authenticate(username, password)
        if token:
            session = rbac.create_session_info(token)
            print(f"✅ {username} ({role}): {len(session['permissions'])} permissions")
        else:
            print(f"❌ {username}: Authentication failed")
    
    print("\n🔍 Permission Matrix:")
    print("=" * 40)
    for role in UserRole:
        permissions = rbac.role_permissions[role]
        print(f"{role.value.upper()}: {', '.join(sorted(permissions))}")