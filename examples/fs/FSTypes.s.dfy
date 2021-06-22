// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "PathSpec.s.dfy"
include "../../lib/Base/Option.s.dfy"

module FSTypes {
  import opened NativeTypes
  import opened Options
  import opened PathSpec

  type Data = seq<byte>

  datatype FileType = 
    | File
    | Directory
    | SymLink(source: Path)
    | CharFile(major: int, minor: int) // device identifier
    | BlockFile(major: int, minor: int) // device identifier
    | FIFOFile
    | SocketFile

  datatype Time = Time(seconds: int, nanoseconds: int)

  // metadata tracked by filesys
  datatype MetaData = MetaData(
    nlink: int,       // number of hard links
    paths: seq<Path>, // paths that are hardlinked to this metadata
    size: int,        // size of file
    ftype: FileType,  // type of file
    perm: int,        // permission
    uid: int,         // user ID
    gid: int,         // group ID
    atime: Time,      // last accessed time
    mtime: Time,      // last modified tme 
    ctime: Time       // last status change time
  )

  predicate ValidNewMetaData(m: MetaData, path: Path)
  {
    && m.atime == m.ctime == m.mtime
    && m.size == 0
    && m.nlink == 1
    && m.paths == [path]
  }

  function EmptyMetaData(): MetaData
  {
    MetaData(0, [], 0, File, 0, 0, 0, Time(0,0), Time(0,0), Time(0,0))
  }

  function InitRootMetaData(): MetaData
  {
    MetaData(1, [RootDir], 0, Directory, 755, 0, 0, Time(0,0), Time(0,0), Time(0,0))
  }

  function EmptyData(): Data
  {
    []
  }

  datatype DirEntry = DirEntry(id: int, path: Path, ftype: FileType)
}