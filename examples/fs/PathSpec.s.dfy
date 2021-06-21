// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../../lib/Lang/NativeTypes.s.dfy"

module PathSpec {
  import opened NativeTypes

  const RootDir :=  ['/' as byte];
  const RootId := 0;
  const DefaultId := -1;
  
  type Path = seq<byte>
  type PathMap = imap<Path, int>

  predicate PathComplete(path_map: PathMap)
  {
    && (forall path :: path in path_map)
  }

  function InitPathMap(): (path_map: PathMap)
  {
    imap path :: if path == RootDir then RootId else DefaultId
  }

  predicate InDir(dir: Path, path: Path)
  {
    && path != dir
    && |path| > |dir|
    && path[..|dir|] == dir
    && path[|dir|] as int == '/' as int
  }

  predicate IsEmptyDir(path_map: PathMap, dir: Path)
  requires PathComplete(path_map)
  {
    && (forall k | InDir(dir, k) :: path_map[k] == DefaultId)
  }

  predicate IsDirEntry(dir: Path, path: Path)
  {
    && InDir(dir, path)
    && !(exists p :: InDir(dir, p) && InDir(p, path))
    // && (forall i | |dir| < i < |path| :: path[i] as int != '/' as int) // equivalent
  }

  function GetParentDir(path: Path): (dir: Path)
  {
    if |path| == 0 then path
    else if path[|path|-1] as int == '/' as int then path[..|path|-1]
    else GetParentDir(path[..|path|-1])
  }

  predicate ValidPath(path_map: PathMap, path: Path)
  requires PathComplete(path_map)
  {
    && path_map[path] != DefaultId
  }

  predicate ValidNewPath(path_map: PathMap, path: Path)
  requires PathComplete(path_map)
  {
    var parentdir := GetParentDir(path);
    && ValidPath(path_map, parentdir)
    && IsDirEntry(parentdir, path)
    && path_map[path] == DefaultId
  }
}