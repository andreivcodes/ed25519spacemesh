library spacemesh_ed25519;

import 'dart:typed_data';
import 'package:cryptography/cryptography.dart';
import 'package:flutter/foundation.dart';
import 'package:spacemesh_ed25519/edwards25519.dart';
import 'package:spacemesh_ed25519/util.dart';

/// PublicKeySize is the size, in bytes, of public keys as used in this package.
const PublicKeySize = 32;

/// PrivateKeySize is the size, in bytes, of private keys as used in this package.
const PrivateKeySize = 64;

/// SignatureSize is the size, in bytes, of signatures generated and verified by this package.
const SignatureSize = 64;

/// SeedSize is the size, in bytes, of private key seeds. These are the private key representations used by RFC 8032.
const SeedSize = 32;

class ED25519 {
  Future<Uint8List> newKeyFromSeed(Uint8List seed) async {
    if (seed.length != SeedSize) {
      throw ArgumentError('ed25519: bad seed length ${seed.length}');
    }
    var h = await Sha512().hash(seed);
    var digest = h.bytes.sublist(0, 32);
    digest[0] &= 248;
    digest[31] &= 127;
    digest[31] |= 64;

    var A = ExtendedGroupElement();
    var hBytes = digest.sublist(0);
    GeScalarMultBase(A, Uint8List.fromList(hBytes));
    var publicKeyBytes = Uint8List(32);
    A.ToBytes(publicKeyBytes);

    var privateKey = Uint8List(PrivateKeySize);
    arrayCopy(seed, 0, privateKey, 0, 32);
    arrayCopy(publicKeyBytes, 0, privateKey, 32, 32);
    return privateKey;
  }

  Future<Uint8List> newDerivedKeyFromSeed(
      Uint8List seed, Uint8List index, Uint8List salt) async {
    final sink = Sha512().newHashSink();
    sink.add(seed);
    sink.add(salt);
    sink.add(index);
    sink.close();
    final hash = await sink.hash();

    final key = newKeyFromSeed(Uint8List.fromList(hash.bytes.sublist(0, 32)));

    return key;
  }

  Future<Uint8List> sign(Uint8List message, Uint8List privateKey) async {
    var h = Sha512().newHashSink();

    h.add(privateKey.sublist(0, 32));

    Uint8List digest1 = new Uint8List(64);
    Uint8List messageDigest = new Uint8List(64);
    Uint8List hramDigest = new Uint8List(64);

    var expandedSecretKeyBuilder = BytesBuilder();
    Uint8List expandedSecretKey = new Uint8List(32);

    h.close();
    var hash = await h.hash();
    digest1 = Uint8List.fromList(hash.bytes);

    expandedSecretKeyBuilder.add(digest1);
    expandedSecretKey = expandedSecretKeyBuilder.toBytes();
    expandedSecretKey[0] &= 248;
    expandedSecretKey[31] &= 63;
    expandedSecretKey[31] |= 64;

    h = Sha512().newHashSink();
    h.add(digest1.sublist(32));
    h.add(message);
    h.close();

    hash = await h.hash();

    messageDigest = Uint8List.fromList(hash.bytes);

    Uint8List messageDigestReduced = new Uint8List(32);

    ScReduce(messageDigestReduced, messageDigest);

    ExtendedGroupElement R = new ExtendedGroupElement();
    GeScalarMultBase(R, messageDigestReduced);

    Uint8List encodedR = new Uint8List(32);

    R.ToBytes(encodedR);

    h = Sha512().newHashSink();
    h.add(encodedR);
    h.add(message);
    h.close();
    hash = await h.hash();

    hramDigest = Uint8List.fromList(hash.bytes);

    Uint8List hramDigestReduced = new Uint8List(32);

    ScReduce(hramDigestReduced, hramDigest);

    Uint8List s = new Uint8List(32);

    ScMulAdd(s, hramDigestReduced, expandedSecretKey, messageDigestReduced);

    var sigBuilder = BytesBuilder();
    Uint8List sig = new Uint8List(SignatureSize);
    sigBuilder.add(encodedR);
    sigBuilder.add(s);
    sig = sigBuilder.toBytes();
    return sig;
  }

  Future<Uint8List> extractPublicKey(Uint8List message, Uint8List sig) async {
    if ((sig.length != SignatureSize) || (sig[63] & 224 != 0)) {
      throw ("ed25519: bad signature format");
    }

    var h = Sha512().newHashSink();

    h.add(sig.sublist(0, 32));
    h.add(message);
    h.close();

    var hash = await h.hash();

    Uint8List digest = Uint8List.fromList(hash.bytes);

    Uint8List hReduced = Uint8List(32);
    ScReduce(hReduced, digest);

    Uint8List hInv = Uint8List(32);
    hInv = InvertModL(hReduced);

    Uint8List s = sig.sublist(32);

    if (s.length != PublicKeySize) {
      throw ("memory copy failed");
    }

    if (!ScMinimal(s)) throw ("invalid sig");

    Uint8List one = new Uint8List(32);
    one[0] = 1;

    ExtendedGroupElement R = new ExtendedGroupElement();
    Uint8List r = sig.sublist(0, 32);
    if (!R.FromBytes(r))
      throw ("failed to create extended group element from s");

    FeNeg(R.X, R.X);
    FeNeg(R.T, R.T);

    ProjectiveGroupElement A = new ProjectiveGroupElement();
    ExtendedGroupElement A2 = new ExtendedGroupElement();
    GeDoubleScalarMultVartime(A, one, R, s);
    A.ToExtended(A2);

    ProjectiveGroupElement ecpk = new ProjectiveGroupElement();
    GeScalarMultVartime(ecpk, hInv, A2);

    Uint8List pubkey = new Uint8List(PublicKeySize);
    ecpk.ToBytes(pubkey);

    return pubkey;
  }

  Future<bool> verify(
      Uint8List publicKey, Uint8List message, Uint8List sig) async {
    if (publicKey.length != PublicKeySize) {
      throw ArgumentError('ed25519: bad publicKey length ${publicKey.length}');
    }
    if (sig.length != SignatureSize || sig[63] & 224 != 0) {
      return false;
    }

    var A = ExtendedGroupElement();
    var publicKeyBytes = Uint8List.fromList(publicKey);
    if (!A.FromBytes(publicKeyBytes)) {
      return false;
    }
    FeNeg(A.X, A.X);
    FeNeg(A.T, A.T);

    var input = Sha512().newHashSink();
    input.add(sig.sublist(0, 32));
    //input.add(publicKeyBytes);
    input.add(message);
    input.close();

    var hash = await input.hash();

    Uint8List digest = Uint8List.fromList(hash.bytes);

    var hReduced = Uint8List(32);
    ScReduce(hReduced, digest as Uint8List);

    var R = ProjectiveGroupElement();
    var s = sig.sublist(32);

    if (!ScMinimal(s)) {
      return false;
    }

    GeDoubleScalarMultVartime(R, hReduced, A, s);

    var checkR = Uint8List(32);
    R.ToBytes(checkR);
    return listEquals(sig.sublist(0, 32), checkR);
  }
}
