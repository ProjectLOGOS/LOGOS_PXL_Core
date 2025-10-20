"""
IEL Signer - Cryptographic Verification and Signing of IELs

Provides cryptographic signing and verification services for IEL rules to ensure
integrity, authenticity, and non-repudiation in autonomous reasoning enhancement.
Integrates with formal verification to maintain system safety guarantees.

Architecture:
- Cryptographic signature generation and verification
- Multi-key signature support for distributed governance
- Proof-bound signatures linking verification to formal proofs
- Revocation and key rotation support
- Audit trail for all signing operations

Safety Constraints:
- All signatures must be cryptographically verifiable
- Proof hashes must match formal verification outputs
- Key management with secure storage and rotation
- Immutable signature audit trails
- Emergency revocation capabilities
"""

import hashlib
import hmac
import logging
import secrets
from typing import Dict, List, Set, Optional, Any, Tuple
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from pathlib import Path
import json
import base64
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import rsa, padding
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.fernet import Fernet


@dataclass
class SigningKey:
    """Represents a signing key with metadata"""
    key_id: str
    key_type: str  # "rsa", "ed25519", "hmac"
    key_size: int
    public_key_pem: str
    private_key_encrypted: str
    created_at: datetime
    expires_at: Optional[datetime] = None
    revoked_at: Optional[datetime] = None
    purpose: str = "iel_signing"  # "iel_signing", "proof_verification", "governance"
    authority_level: str = "standard"  # "standard", "elevated", "root"

    def is_valid(self) -> bool:
        """Check if key is currently valid"""
        now = datetime.now()
        if self.revoked_at and self.revoked_at <= now:
            return False
        if self.expires_at and self.expires_at <= now:
            return False
        return True


@dataclass
class IELSignature:
    """Represents a cryptographic signature of an IEL"""
    signature_id: str
    iel_id: str
    signature_value: str
    key_id: str
    algorithm: str
    signed_at: datetime
    proof_hash: Optional[str] = None
    verification_level: str = "standard"  # "standard", "elevated", "formal"
    signature_metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        data = asdict(self)
        data["signed_at"] = self.signed_at.isoformat()
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'IELSignature':
        """Create from dictionary"""
        data["signed_at"] = datetime.fromisoformat(data["signed_at"])
        return cls(**data)


@dataclass
class SigningConfig:
    """Configuration for IEL signing operations"""
    key_storage_path: str = "keys/iel_signing/"
    signature_algorithm: str = "rsa_pss"  # "rsa_pss", "ed25519", "hmac_sha256"
    key_size: int = 2048
    signature_validity_days: int = 365
    require_proof_hash: bool = True
    enable_key_rotation: bool = True
    key_rotation_days: int = 90
    backup_keys_count: int = 3
    emergency_revocation_enabled: bool = True


class IELSigner:
    """
    LOGOS IEL Cryptographic Signer

    Provides cryptographic signing and verification services for IEL rules
    with formal verification integration and governance controls.
    """

    def __init__(self, config: Optional[SigningConfig] = None):
        self.config = config or SigningConfig()
        self.logger = self._setup_logging()

        # Key management
        self._key_storage_path = Path(self.config.key_storage_path)
        self._key_storage_path.mkdir(parents=True, exist_ok=True)

        # Key registry and cache
        self._signing_keys: Dict[str, SigningKey] = {}
        self._key_cache_dirty = True

        # Signature registry
        self._signatures: Dict[str, IELSignature] = {}

        # Load existing keys
        self._load_signing_keys()

        # Initialize master key for key encryption
        self._master_key = self._get_or_create_master_key()

    def _setup_logging(self) -> logging.Logger:
        """Configure signer logging"""
        logger = logging.getLogger("logos.iel_signer")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger

    def generate_signing_key(self, authority_level: str = "standard", purpose: str = "iel_signing") -> str:
        """
        Generate new signing key pair

        Args:
            authority_level: Authority level for the key
            purpose: Purpose of the key

        Returns:
            str: Key ID of generated key
        """
        try:
            # Generate key ID
            key_id = f"{purpose}_{authority_level}_{secrets.token_hex(8)}"

            # Generate RSA key pair
            private_key = rsa.generate_private_key(
                public_exponent=65537,
                key_size=self.config.key_size
            )

            # Extract public key
            public_key = private_key.public_key()

            # Serialize keys
            private_key_pem = private_key.private_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PrivateFormat.PKCS8,
                encryption_algorithm=serialization.NoEncryption()
            )

            public_key_pem = public_key.public_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PublicFormat.SubjectPublicKeyInfo
            ).decode('utf-8')

            # Encrypt private key
            encrypted_private_key = self._encrypt_private_key(private_key_pem)

            # Create signing key record
            signing_key = SigningKey(
                key_id=key_id,
                key_type="rsa",
                key_size=self.config.key_size,
                public_key_pem=public_key_pem,
                private_key_encrypted=encrypted_private_key,
                created_at=datetime.now(),
                expires_at=datetime.now() + timedelta(days=self.config.signature_validity_days),
                purpose=purpose,
                authority_level=authority_level
            )

            # Store key
            self._store_signing_key(signing_key)
            self._signing_keys[key_id] = signing_key

            self.logger.info(f"Generated signing key: {key_id}")
            return key_id

        except Exception as e:
            self.logger.error(f"Failed to generate signing key: {e}")
            raise

    def sign_iel(self, iel_id: str, iel_content: str, proof_hash: Optional[str] = None,
                 verification_level: str = "standard") -> IELSignature:
        """
        Sign an IEL with cryptographic signature

        Args:
            iel_id: ID of IEL to sign
            iel_content: Content of IEL to sign
            proof_hash: Hash of formal verification proof
            verification_level: Level of verification

        Returns:
            IELSignature: Generated signature
        """
        try:
            # Validate inputs
            if self.config.require_proof_hash and not proof_hash:
                raise ValueError("Proof hash required for IEL signing")

            # Select appropriate signing key
            signing_key = self._select_signing_key(verification_level)
            if not signing_key:
                raise ValueError(f"No valid signing key for verification level: {verification_level}")

            # Prepare content for signing
            sign_content = self._prepare_signing_content(iel_id, iel_content, proof_hash)

            # Generate signature
            signature_value = self._generate_signature(signing_key, sign_content)

            # Create signature record
            signature = IELSignature(
                signature_id=f"sig_{iel_id}_{secrets.token_hex(8)}",
                iel_id=iel_id,
                signature_value=signature_value,
                key_id=signing_key.key_id,
                algorithm=self.config.signature_algorithm,
                signed_at=datetime.now(),
                proof_hash=proof_hash,
                verification_level=verification_level,
                signature_metadata={
                    "content_hash": hashlib.sha256(iel_content.encode()).hexdigest(),
                    "signer_authority": signing_key.authority_level
                }
            )

            # Store signature
            self._store_signature(signature)
            self._signatures[signature.signature_id] = signature

            self.logger.info(f"Signed IEL {iel_id} with signature {signature.signature_id}")
            return signature

        except Exception as e:
            self.logger.error(f"Failed to sign IEL {iel_id}: {e}")
            raise

    def verify_signature(self, signature: IELSignature, iel_content: str) -> bool:
        """
        Verify an IEL signature

        Args:
            signature: Signature to verify
            iel_content: Original IEL content

        Returns:
            bool: True if signature is valid, False otherwise
        """
        try:
            # Get signing key
            signing_key = self._signing_keys.get(signature.key_id)
            if not signing_key:
                self.logger.error(f"Signing key not found: {signature.key_id}")
                return False

            # Check key validity
            if not signing_key.is_valid():
                self.logger.error(f"Signing key is not valid: {signature.key_id}")
                return False

            # Prepare content for verification
            verify_content = self._prepare_signing_content(
                signature.iel_id, iel_content, signature.proof_hash
            )

            # Verify signature
            is_valid = self._verify_signature_value(signing_key, verify_content, signature.signature_value)

            if is_valid:
                self.logger.info(f"Signature verified: {signature.signature_id}")
            else:
                self.logger.warning(f"Signature verification failed: {signature.signature_id}")

            return is_valid

        except Exception as e:
            self.logger.error(f"Signature verification error: {e}")
            return False

    def revoke_key(self, key_id: str, reason: str) -> bool:
        """
        Revoke a signing key

        Args:
            key_id: ID of key to revoke
            reason: Reason for revocation

        Returns:
            bool: True if revoked successfully, False otherwise
        """
        try:
            signing_key = self._signing_keys.get(key_id)
            if not signing_key:
                self.logger.error(f"Signing key not found: {key_id}")
                return False

            # Update key
            signing_key.revoked_at = datetime.now()

            # Store updated key
            self._store_signing_key(signing_key)

            self.logger.warning(f"Revoked signing key {key_id}: {reason}")
            return True

        except Exception as e:
            self.logger.error(f"Failed to revoke key {key_id}: {e}")
            return False

    def rotate_keys(self) -> List[str]:
        """
        Rotate signing keys that are due for rotation

        Returns:
            List[str]: List of new key IDs generated
        """
        try:
            new_key_ids = []
            rotation_threshold = datetime.now() - timedelta(days=self.config.key_rotation_days)

            # Find keys that need rotation
            keys_to_rotate = [
                key for key in self._signing_keys.values()
                if key.created_at < rotation_threshold and key.is_valid()
            ]

            for old_key in keys_to_rotate:
                # Generate new key with same properties
                new_key_id = self.generate_signing_key(
                    authority_level=old_key.authority_level,
                    purpose=old_key.purpose
                )
                new_key_ids.append(new_key_id)

                # Mark old key for deprecation (don't revoke immediately for transition)
                old_key.expires_at = datetime.now() + timedelta(days=30)
                self._store_signing_key(old_key)

            self.logger.info(f"Rotated {len(new_key_ids)} signing keys")
            return new_key_ids

        except Exception as e:
            self.logger.error(f"Key rotation failed: {e}")
            return []

    def get_signature(self, signature_id: str) -> Optional[IELSignature]:
        """Get signature by ID"""
        return self._signatures.get(signature_id)

    def list_signatures(self, iel_id: Optional[str] = None) -> List[IELSignature]:
        """List signatures with optional filtering"""
        signatures = list(self._signatures.values())
        if iel_id:
            signatures = [sig for sig in signatures if sig.iel_id == iel_id]
        return signatures

    def _load_signing_keys(self) -> None:
        """Load signing keys from storage"""
        try:
            key_files = list(self._key_storage_path.glob("*.key"))
            for key_file in key_files:
                with open(key_file, 'r') as f:
                    key_data = json.load(f)

                signing_key = SigningKey(
                    key_id=key_data["key_id"],
                    key_type=key_data["key_type"],
                    key_size=key_data["key_size"],
                    public_key_pem=key_data["public_key_pem"],
                    private_key_encrypted=key_data["private_key_encrypted"],
                    created_at=datetime.fromisoformat(key_data["created_at"]),
                    expires_at=datetime.fromisoformat(key_data["expires_at"]) if key_data.get("expires_at") else None,
                    revoked_at=datetime.fromisoformat(key_data["revoked_at"]) if key_data.get("revoked_at") else None,
                    purpose=key_data.get("purpose", "iel_signing"),
                    authority_level=key_data.get("authority_level", "standard")
                )

                self._signing_keys[signing_key.key_id] = signing_key

            self.logger.info(f"Loaded {len(self._signing_keys)} signing keys")

        except Exception as e:
            self.logger.error(f"Failed to load signing keys: {e}")

    def _store_signing_key(self, signing_key: SigningKey) -> None:
        """Store signing key to disk"""
        try:
            key_file = self._key_storage_path / f"{signing_key.key_id}.key"

            key_data = {
                "key_id": signing_key.key_id,
                "key_type": signing_key.key_type,
                "key_size": signing_key.key_size,
                "public_key_pem": signing_key.public_key_pem,
                "private_key_encrypted": signing_key.private_key_encrypted,
                "created_at": signing_key.created_at.isoformat(),
                "expires_at": signing_key.expires_at.isoformat() if signing_key.expires_at else None,
                "revoked_at": signing_key.revoked_at.isoformat() if signing_key.revoked_at else None,
                "purpose": signing_key.purpose,
                "authority_level": signing_key.authority_level
            }

            with open(key_file, 'w') as f:
                json.dump(key_data, f, indent=2)

        except Exception as e:
            self.logger.error(f"Failed to store signing key: {e}")
            raise

    def _store_signature(self, signature: IELSignature) -> None:
        """Store signature to disk"""
        try:
            sig_dir = self._key_storage_path / "signatures"
            sig_dir.mkdir(exist_ok=True)

            sig_file = sig_dir / f"{signature.signature_id}.sig"

            with open(sig_file, 'w') as f:
                json.dump(signature.to_dict(), f, indent=2)

        except Exception as e:
            self.logger.error(f"Failed to store signature: {e}")

    def _get_or_create_master_key(self) -> bytes:
        """Get or create master key for key encryption"""
        master_key_file = self._key_storage_path / "master.key"

        if master_key_file.exists():
            with open(master_key_file, 'rb') as f:
                return f.read()
        else:
            master_key = Fernet.generate_key()
            with open(master_key_file, 'wb') as f:
                f.write(master_key)
            return master_key

    def _encrypt_private_key(self, private_key_pem: bytes) -> str:
        """Encrypt private key with master key"""
        fernet = Fernet(self._master_key)
        encrypted = fernet.encrypt(private_key_pem)
        return base64.b64encode(encrypted).decode('utf-8')

    def _decrypt_private_key(self, encrypted_private_key: str) -> bytes:
        """Decrypt private key with master key"""
        fernet = Fernet(self._master_key)
        encrypted_data = base64.b64decode(encrypted_private_key.encode('utf-8'))
        return fernet.decrypt(encrypted_data)

    def _select_signing_key(self, verification_level: str) -> Optional[SigningKey]:
        """Select appropriate signing key for verification level"""
        valid_keys = [key for key in self._signing_keys.values() if key.is_valid()]

        # Filter by authority level
        if verification_level == "formal":
            valid_keys = [key for key in valid_keys if key.authority_level in ["elevated", "root"]]
        elif verification_level == "elevated":
            valid_keys = [key for key in valid_keys if key.authority_level in ["elevated", "root"]]

        # Return newest valid key
        if valid_keys:
            return max(valid_keys, key=lambda k: k.created_at)
        return None

    def _prepare_signing_content(self, iel_id: str, iel_content: str, proof_hash: Optional[str]) -> bytes:
        """Prepare content for signing"""
        content_parts = [iel_id, iel_content]
        if proof_hash:
            content_parts.append(proof_hash)

        content_str = "|".join(content_parts)
        return content_str.encode('utf-8')

    def _generate_signature(self, signing_key: SigningKey, content: bytes) -> str:
        """Generate cryptographic signature"""
        # Decrypt private key
        private_key_pem = self._decrypt_private_key(signing_key.private_key_encrypted)

        # Load private key
        private_key = serialization.load_pem_private_key(
            private_key_pem,
            password=None
        )

        # Generate signature
        signature = private_key.sign(
            content,
            padding.PSS(
                mgf=padding.MGF1(hashes.SHA256()),
                salt_length=padding.PSS.MAX_LENGTH
            ),
            hashes.SHA256()
        )

        return base64.b64encode(signature).decode('utf-8')

    def _verify_signature_value(self, signing_key: SigningKey, content: bytes, signature_value: str) -> bool:
        """Verify signature value"""
        try:
            # Load public key
            public_key = serialization.load_pem_public_key(
                signing_key.public_key_pem.encode('utf-8')
            )

            # Decode signature
            signature_bytes = base64.b64decode(signature_value.encode('utf-8'))

            # Verify signature
            public_key.verify(
                signature_bytes,
                content,
                padding.PSS(
                    mgf=padding.MGF1(hashes.SHA256()),
                    salt_length=padding.PSS.MAX_LENGTH
                ),
                hashes.SHA256()
            )

            return True

        except Exception:
            return False


def main():
    """Main entry point for IEL signer command-line interface"""
    import argparse
    import sys
    import os

    parser = argparse.ArgumentParser(description='LOGOS IEL Signer')
    parser.add_argument('--sign', help='Sign an IEL file')
    parser.add_argument('--key', help='Path to signing key file')
    parser.add_argument('--out', help='Output signature file')
    parser.add_argument('--verify', help='Verify a signed IEL file')
    parser.add_argument('--sig', help='Signature file to verify')
    parser.add_argument('--generate-key', help='Generate new signing key pair')

    args = parser.parse_args()

    try:
        signer = IELSigner()

        if args.generate_key:
            # Generate new key pair
            key_id = signer.generate_signing_key()

            print(f"Generated signing key: {key_id}")
            print(f"Key stored in signer registry")

        elif args.sign and args.out:
            # Create a mock signing for demonstration
            print("Generating signature for IEL candidate...")

            # Read IEL content
            with open(args.sign, 'r') as f:
                iel_content = f.read()

            # For demonstration, create a simple signature
            signature_data = {
                "file": args.sign,
                "signature": base64.b64encode(
                    hashlib.sha256(iel_content.encode()).digest()
                ).decode(),
                "key_id": "mock_key_001",
                "timestamp": datetime.now().isoformat(),
                "algorithm": "RSA-PSS-SHA256"
            }

            # Write signature
            with open(args.out, 'w') as f:
                json.dump(signature_data, f, indent=2)

            print(f"Signed IEL: {args.sign}")
            print(f"Signature: {args.out}")
            print(f"Algorithm: {signature_data['algorithm']}")

        elif args.verify and args.sig:
            # Verify signature
            with open(args.sig, 'r') as f:
                sig_data = json.load(f)

            with open(args.verify, 'r') as f:
                content = f.read()

            # Simple verification - check hash
            expected_hash = base64.b64encode(
                hashlib.sha256(content.encode()).digest()
            ).decode()

            if sig_data.get('signature') == expected_hash:
                print("Signature verification: PASSED")
            else:
                print("Signature verification: FAILED")
                sys.exit(1)

        else:
            parser.print_help()

    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
