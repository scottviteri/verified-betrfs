// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause


include "FSTypes.s.dfy"
include "../../lib/Lang/System/SeqComparison.s.dfy"

/*
 * This file system doesn't specify any permission checking or path cleanup: relying on shim/vfs to do so.
 * It defines an in memory filesystem, has no knowledge of device and persistence.
*/

module FileSystem {
  import opened FSTypes
  import opened PathSpec
  import opened Options
  import SeqComparison

  type MetaView = imap<int, MetaData>
  type DataView = imap<int, Data> 

  datatype FileSys = FileSys(path_map: PathMap, meta_map: MetaView, data_map: DataView)

  predicate WF(fs: FileSys)
  {
    && PathComplete(fs.path_map)
    && (forall id :: id in fs.meta_map && id in fs.data_map)
  }

  predicate Init(fs: FileSys)
  {
    && fs.path_map == InitPathMap()
    && fs.meta_map == (imap id :: if id == RootId then InitRootMetaData() else EmptyMetaData())
    && fs.data_map == (imap id :: EmptyData())
  }

  /// Inv conditions

  predicate ValidLinks(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var id := fs.path_map[path];
    var m := fs.meta_map[id];
    && m.nlink == |m.paths|
    && (m.ftype.Directory? ==> m.nlink == 1)
    && (forall i, j | 0 <= i < j < |m.paths| :: m.paths[i] != m.paths[j]) // paths are unique
  }

  predicate NoUnknownLinks(fs: FileSys, id: int)
  requires WF(fs)
  {
    var m := fs.meta_map[id];
    && (forall path :: if path in m.paths then fs.path_map[path] == id else fs.path_map[path] != id)
    // && (forall path | ValidPath(fs, path) && fs.path_map[path] == id :: path in m.paths)
  }

  predicate ParentDirIsDir(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var parentdir := GetParentDir(path);
    && ValidPath(fs, parentdir)
    && fs.meta_map[fs.path_map[parentdir]].ftype.Directory?
  }

  predicate ConsistentData(fs: FileSys, path: Path)
  requires WF(fs)
  {
    var id := fs.path_map[path];
    && fs.meta_map[id].size == |fs.data_map[id]|
  }

  predicate ValidPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && fs.path_map[path] != DefaultId
  }

  predicate ValidNewPath(fs: FileSys, path: Path)
  requires WF(fs)
  {
    && ParentDirIsDir(fs, path)
    && IsDirEntry(GetParentDir(path), path)
    && fs.path_map[path] == DefaultId
    // var parentdir := GetParentDir(path);
    // && ValidPath(fs, parentdir)
    // && fs.meta_map[fs.path_map[parentdir]].ftype.Directory?
  }


  /// FileSys Ops

  predicate GetAttr(fs: FileSys, fs':FileSys, path: Path, attr: MetaData)
  {
    && WF(fs)
    && ValidPath(fs, path)
    && fs' == fs
    && attr == fs.meta_map[fs.path_map[path]]
  }

  predicate ReadLink(fs: FileSys, fs':FileSys, path: Path, link_path: Path)
  {
    && WF(fs)
    && ValidPath(fs, path)
    && fs' == fs
    && fs.meta_map[fs.path_map[path]].ftype.SymLink?
    && link_path == fs.meta_map[fs.path_map[path]].ftype.source
  }

  predicate Create(fs: FileSys, fs':FileSys, path: Path, id: int, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, path)
    && ValidNewMetaData(m, path)
    && id != DefaultId
    // Entry Not Present
    && fs.meta_map[id] == EmptyMetaData()
    && fs.data_map[id] == EmptyData()
    // Updated maps
    && fs'.path_map == fs.path_map[path := id]
    && fs'.meta_map == fs.meta_map[id := m]
    && fs'.data_map == fs.data_map
  }

  function MetaDataUpdateLink(m: MetaData, delta: int, paths: seq<Path>, ctime: Time): MetaData
  {
    MetaData(m.nlink+delta, paths, m.size, m.ftype, m.perm, m.uid, m.gid, m.atime, m.mtime, ctime)
  }

  function RemovePath(paths: seq<Path>, path: Path) : seq<Path>
  {
    if path in paths then (
      var i :| 0 <= i < |paths| && paths[i] == path;
      paths[..i] + paths[i+1..]
    ) else (
      paths
    )
  }

  function MetaDataDelete(fs: FileSys, path: Path, id: int, ctime: Time): MetaData
  requires WF(fs)
  requires id != DefaultId
  {
    var m := fs.meta_map[id];
    if m.nlink == 1
    then EmptyMetaData()
    else MetaDataUpdateLink(m, -1, RemovePath(m.paths, path), ctime)
  }

  function DataDelete(fs: FileSys, id: int): Data
  requires WF(fs)
  requires id != DefaultId
  {
    if fs.meta_map[id].nlink == 1
    then EmptyData()
    else fs.data_map[id]
  }

  predicate Delete(fs: FileSys, fs':FileSys, path: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && path != RootDir
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && (fs.meta_map[id].ftype.Directory? ==> IsEmptyDir(fs.path_map, path))
    // maps after delete
    && fs'.path_map == fs.path_map[path := DefaultId]
    && fs'.meta_map == fs.meta_map[id := MetaDataDelete(fs, path, id, ctime)]
    && fs'.data_map == fs.data_map[id := DataDelete(fs, id)]
  }

  predicate SymLink(fs: FileSys, fs':FileSys, source: Path, dest: Path, id: int, m: MetaData)
  {
    && WF(fs)
    && WF(fs')
    && ValidNewPath(fs, dest) // source doesn't need to be valid
    && ValidNewMetaData(m, dest)
    && m.ftype == FileType.SymLink(source)
    && id != DefaultId
    && fs.meta_map[id] == EmptyMetaData()
    && fs.data_map[id] == EmptyData()
    // updated maps
    && fs'.path_map == fs.path_map[dest := id]
    && fs'.meta_map == fs.meta_map[id := m]
    && fs'.data_map == fs.data_map
  }

  function PathMapRenameDir(fs: FileSys, src: Path, dst: Path): PathMap
  requires WF(fs)
  {
    imap path :: 
      // remove source paths
      if path == src || InDir(src, path) then DefaultId
      // redirect renamed paths to point to the same ids as source
      else if path == dst then fs.path_map[src]
      else if InDir(dst, path) then fs.path_map[src + path[|dst|+1..]]
      // everything else remains the same
      else fs.path_map[path]
  }

  predicate RenameDir(fs: FileSys, fs':FileSys, src: Path, dst: Path, ctime: Time)
  requires WF(fs)
  requires WF(fs')
  requires ValidPath(fs, src)
  requires ValidPath(fs, dst) || ValidNewPath(fs, dst)
  {
    var src_id := fs.path_map[src];
    var dst_id := fs.path_map[dst];
    var src_m := fs.meta_map[src_id];
    var src_m' := MetaDataUpdateTime(src_m, src_m.atime, src_m.mtime, ctime);
    && src_m.ftype.Directory?
    && (ValidPath(fs, dst) ==>
      && fs.meta_map[fs.path_map[dst]].ftype.Directory?
      && IsEmptyDir(fs.path_map, dst))
    // updated maps
    && fs'.path_map == PathMapRenameDir(fs, src, dst)
    && fs'.meta_map == (
      if ValidPath(fs, dst)
      then fs.meta_map[src_id := src_m'][dst_id := EmptyMetaData()]
      else fs.meta_map[src_id := src_m'])
    && fs'.data_map == fs.data_map
  }

  predicate RenameNonDir(fs: FileSys, fs':FileSys, src: Path, dst: Path, ctime: Time)
  requires WF(fs)
  requires WF(fs')
  requires ValidPath(fs, src)
  requires ValidPath(fs, dst) || ValidNewPath(fs, dst)
  {
    var src_id := fs.path_map[src];
    var dst_id := fs.path_map[dst];
    var src_m := fs.meta_map[src_id];
    var src_m' := MetaDataUpdateTime(src_m, src_m.atime, src_m.mtime, ctime);
    && !src_m.ftype.Directory? // file, symlink, dev file, fifo, socket
    && (ValidPath(fs, dst) ==> !fs.meta_map[dst_id].ftype.Directory?)
    // updated maps
    && fs'.path_map == fs.path_map[dst := src_id][src := DefaultId]
    && fs'.meta_map == (
      if ValidPath(fs, dst)
      then fs.meta_map[src_id := src_m'][dst_id := MetaDataDelete(fs, dst, dst_id, ctime)]
      else fs.meta_map[src_id := src_m'])
    && fs'.data_map == (
      if ValidPath(fs, dst)
      then fs.data_map[dst_id := DataDelete(fs, dst_id)]
      else fs.data_map)
  }

  // rename is a map because we allow directory
  predicate Rename(fs: FileSys, fs':FileSys, src: Path, dst: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, src)
    && !(|dst| >= |src| && dst[..|src|] == src) // src can't be a prefix of dst
    && (ValidPath(fs, dst) || ValidNewPath(fs, dst))
    && var src_m := fs.meta_map[fs.path_map[src]];
    && (src_m.ftype.Directory? ==> RenameDir(fs, fs', src, dst, ctime))
    && (!src_m.ftype.Directory? ==> RenameNonDir(fs, fs', src, dst, ctime))
  }

  predicate Link(fs: FileSys, fs':FileSys, source: Path, dest: Path, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, source)  // NOTE: won't work for hardlink other filesystem files
    && ValidNewPath(fs, dest)
    && var id := fs.path_map[source];
    && var m := fs.meta_map[id];
    && !m.ftype.Directory?  // disallow directory hardlinks
    // updated maps
    && fs'.path_map == fs.path_map[dest := id]
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateLink(m, 1, m.paths + [dest], ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataChangeAttr(m: MetaData, perm: int, uid:int, gid: int, ctime: Time): MetaData
  {
    MetaData(m.nlink, m.paths, m.size, m.ftype, perm, uid, gid, m.atime, m.mtime, ctime)
  }

  // chown + chmod
  predicate ChangeAttr(fs: FileSys, fs':FileSys, path: Path, perm: int, uid: int, gid: int, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataChangeAttr(fs.meta_map[id], perm, uid, gid, ctime)]
    && fs'.data_map == fs.data_map
  }

  function MetaDataTruncate(m: MetaData, size: int, time: Time): MetaData
  {
    MetaData(m.nlink, m.paths, size, m.ftype, m.perm, m.uid, m.gid, m.atime, time, time)
  }

  function ZeroData(size: int) : (d: Data)
  requires size >= 0
  ensures size == |d|
  ensures forall i | 0 <= i < |d| :: d[i] == 0
  {
    if size == 0 then [] else ZeroData(size-1) + [0]
  }

  function DataTruncate(d: Data, size: int): (d': Data)
  requires 0 <= size
  ensures |d'| == size
  {
    if |d| >= size then d[..size] else d + ZeroData(size-|d|)
  }

  predicate Truncate(fs: FileSys, fs':FileSys, path: Path, size: int, time: Time)
  {
    && WF(fs)
    && WF(fs')
    && 0 <= size
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && size != fs.meta_map[id].size
    // updated maps
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataTruncate(fs.meta_map[id], size, time)]
    && fs'.data_map == fs.data_map[id := DataTruncate(fs.data_map[id], size)]
  }

  predicate Read(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data)
  {
    && WF(fs)
    && fs' == fs
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && 0 <= offset <= offset+size <= fs.meta_map[id].size
    && fs.meta_map[id].size == |fs.data_map[id]| // consistency
    && data == fs.data_map[id][offset..offset+size]
  }

  function MetaDataWrite(m: MetaData, newsize: int, time: Time): MetaData
  {
    var size := if m.size > newsize then m.size else newsize;
    MetaData(m.nlink, m.paths, size, m.ftype, m.perm, m.uid, m.gid, time, time, time)
  }

  function DataWrite(d: Data, data: Data, offset: int, size: int): (d': Data)
  requires 0 <= offset <= |d|
  requires size == |data|
  ensures offset <= offset+size <= |d'|
  ensures d'[offset..offset+size] == data
  {
    if offset+size > |d| then d[..offset] + data else d[..offset] + data + d[offset+size..]
  }

  predicate Write(fs: FileSys, fs':FileSys, path: Path, offset: int, size: int, data: Data, time: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, path)
    && |data| == size
    && var id := fs.path_map[path];
    && fs.meta_map[id].ftype.File?
    && fs.meta_map[id].size == |fs.data_map[id]|
    && 0 <= offset <= fs.meta_map[id].size
    // updated maps
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataWrite(fs.meta_map[id], offset+size, time)]
    && fs'.data_map == fs.data_map[id := DataWrite(fs.data_map[id], data, offset, size)]
  }

  function MetaDataUpdateTime(m: MetaData, atime: Time, mtime: Time, ctime: Time): MetaData
  {
    MetaData(m.nlink, m.paths, m.size, m.ftype, m.perm, m.uid, m.gid, atime, mtime, ctime)
  }

  predicate UpdateTime(fs: FileSys, fs':FileSys, path: Path, atime: Time, mtime: Time, ctime: Time)
  {
    && WF(fs)
    && WF(fs')
    && ValidPath(fs, path)
    && var id := fs.path_map[path];
    && fs'.path_map == fs.path_map
    && fs'.meta_map == fs.meta_map[id := MetaDataUpdateTime(fs.meta_map[id], atime, mtime, ctime)]
    && fs'.data_map == fs.data_map
  }

  predicate ValidDirEntry(fs: FileSys, de: DirEntry)
  requires WF(fs)
  {
    && ValidPath(fs, de.path) // valid path
    && de.id == fs.path_map[de.path]
    && de.ftype == fs.meta_map[de.id].ftype
  }

  predicate ReadDir(fs: FileSys, fs':FileSys, dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
  {
    && WF(fs)
    && fs' == fs
    && ValidPath(fs, dir)
    && fs.meta_map[fs.path_map[dir]].ftype.Directory?
    && (start.Some? ==> InDir(dir, start.value))
    // results consistent with filesys content
    && (forall i | 0 <= i < |results| :: ValidDirEntry(fs, results[i]))
    // results actually belong to this directory
    && (forall i | 0 <= i < |results| :: IsDirEntry(dir, results[i].path))
    // results are strictly sorted
    && (forall i, j | 0 <= i < j < |results| :: SeqComparison.lt(results[i].path, results[j].path))
    // results don't skip over any valid entry
    && (forall path |
        && IsDirEntry(dir, path)
        && ValidPath(fs, path)
        && (start.Some? ==> SeqComparison.lte(path, start.value))
        && (!done && |results| > 0 ==> SeqComparison.lt(results[|results|-1].path, path))
        :: (exists i :: 0 <= i < |results| && results[i].path == path))
  }

  predicate Stutter(fs: FileSys, fs': FileSys)
  {
    && WF(fs)
    && fs' == fs
  }

  datatype Step =
    | GetAttrStep(path: Path, attr: MetaData)
    | ReadLinkStep(path: Path, link_path: Path)
    | CreateStep(path: Path, id: int, m: MetaData) // mknod and mkdir
    | DeleteStep(path: Path, ctime: Time) // unlink and rmdir
    | SymLinkStep(source: Path, dest: Path, id: int, m: MetaData)
    | RenameStep(source: Path, dest: Path, ctime: Time)
    | LinkStep(source: Path, dest: Path, ctime: Time)
    | ChangeAttrStep(path: Path, perm: int, uid: int, gid: int, ctime: Time) // chmod + chown
    | TruncateStep(path: Path, size: int, time: Time)
    | ReadStep(path: Path, offset: int, size: int, data: Data)
    | WriteStep(path: Path, offset: int, size: int, data: Data, time: Time)
    | UpdateTimeStep(path: Path, atime: Time, mtime: Time, ctime: Time) 
    | ReadDirStep(dir: Path, start: Option<Path>, results: seq<DirEntry>, done: bool)
    | StutterStep

  predicate NextStep(fs: FileSys, fs': FileSys, step:Step)
  {
    match step {
      case GetAttrStep(path, attr) => GetAttr(fs, fs', path, attr)
      case ReadLinkStep(path, link_path) => ReadLink(fs, fs', path, link_path)
      case CreateStep(path, id, m) => Create(fs, fs', path, id, m)
      case DeleteStep(path, ctime) => Delete(fs, fs', path, ctime)
      case SymLinkStep(source, dest, id, m) => SymLink(fs, fs', source, dest, id, m)
      case RenameStep(source, dest, ctime) => Rename(fs, fs', source, dest, ctime)
      case LinkStep(source, dest, ctime) => Link(fs, fs', source, dest, ctime)
      case ChangeAttrStep(path, perm, uid, gid, ctime) => ChangeAttr(fs, fs', path, perm, uid, gid, ctime)
      case TruncateStep(path, size, time) => Truncate(fs, fs', path, size, time)
      case ReadStep(path, offset, size, data) => Read(fs, fs', path, offset, size, data)
      case WriteStep(path, offset, size, data, time) => Write(fs, fs', path, offset, size, data, time)
      case UpdateTimeStep(path, atime, mtime, ctime) => UpdateTime(fs, fs', path, atime, mtime, ctime)
      case ReadDirStep(dir, start, results, done) => ReadDir(fs, fs', dir, start, results, done)
      case StutterStep() => Stutter(fs, fs')
    }
  }

  predicate Next(fs: FileSys, fs': FileSys)
  {
    exists step :: NextStep(fs, fs', step)
  }

  predicate Inv(fs: FileSys)
  {
    && WF(fs)
    // DefaultId is never occupied
    && fs.meta_map[DefaultId] == EmptyMetaData()
    && fs.data_map[DefaultId] == EmptyData()
    // Path map internal invariant :: all valid paths must be greater than 0
    && (forall path | ValidPath(fs, path) :: |path| > 0) // all valid path must 
    // Metadata map internal consistency: nlink consitency and directory has no hardlinks
    && (forall path :: ValidLinks(fs, path))
    // Meta and data map consistency: metadata size is consistent with actual data size
    && (forall path :: ConsistentData(fs, path))
    // Path and meta map consistency: directory structure is connected
    && (forall path | ValidPath(fs, path) && path != RootDir :: ParentDirIsDir(fs, path))
    // Path and meta map consistency: allocated path has non empty metadata
    && (forall path | ValidPath(fs, path) :: fs.meta_map[fs.path_map[path]] != EmptyMetaData())
    // Path and meta map consistency: paths is consistent with ids mapped from path_map
    && (forall id | fs.meta_map[id] != EmptyMetaData() :: NoUnknownLinks(fs, id))
  }

  lemma InitImpliesInv(fs: FileSys)
  requires Init(fs)
  ensures Inv(fs)
  {
  }

  // TODO: add ui op
  lemma NextPreservesInv(fs: FileSys, fs': FileSys)
  requires Inv(fs)
  requires Next(fs, fs')
  ensures Inv(fs')
  {
    var step :| NextStep(fs, fs', step);
    NextStepPreservesInv(fs, fs', step);
  }

  lemma NextStepPreservesInv(fs: FileSys, fs': FileSys, step: Step)
  requires Inv(fs)
  requires NextStep(fs, fs', step)
  ensures Inv(fs')
  {
    match step {
      case DeleteStep(path, ctime) => DeletePreservesInv(fs, fs', path, ctime);
      case RenameStep(source, dest, ctime) => RenamePreservesInv(fs, fs', source, dest, ctime);   
      case LinkStep(source, dest, ctime) => LinkPreservesInv(fs, fs', source, dest, ctime);
      case _ => { 
        if step.CreateStep? || step.SymLinkStep? || step.ChangeAttrStep? 
        || step.TruncateStep? || step.WriteStep? || step.UpdateTimeStep? {
          SimpleStepPreservesInv(fs, fs', step);
        }
      }
    }
  }

  /// Invariant proofs

  lemma RemovePathCorrect(paths: seq<Path>, path: Path)
  requires path in paths
  requires forall i, j | 0 <= i < j < |paths| :: paths[i] != paths[j]
  ensures path !in RemovePath(paths, path)
  {
  }

  lemma DeletePreservesInv(fs: FileSys, fs': FileSys, path: Path, ctime: Time)
  requires Inv(fs)
  requires Delete(fs, fs', path, ctime)
  ensures Inv(fs')
  {
    forall p
    ensures ValidLinks(fs', p)
    ensures ConsistentData(fs', p)
    {
      if p != path {
        assert ValidLinks(fs, p); // observe
        assert ConsistentData(fs, p); // observe
      }
    }

    forall p | ValidPath(fs', p)
    ensures |p| > 0
    ensures fs'.meta_map[fs'.path_map[p]] != EmptyMetaData()
    ensures p != RootDir ==> ParentDirIsDir(fs', p)
    {
      assert |p| > 0; // observe
      assert p != path;

      var id := fs.path_map[path];
      var m := fs.meta_map[id];
      
      assert ValidLinks(fs, path); // observe
      assert m.nlink == |m.paths|;

      if m.nlink == 1 {
        assert m.paths == [path];
        assert NoUnknownLinks(fs, id);
        assert fs.path_map[p] != id;
      } else {
        assert m.nlink > 1;
        if fs'.path_map[p] == id {
          assert fs'.meta_map[id] != EmptyMetaData();
        }
      }

      assert fs'.meta_map[fs'.path_map[p]] != EmptyMetaData();

      if p != RootDir {
        var parent_dir := GetParentDir(p);
        var parent_id := fs.path_map[parent_dir];
        var parent_meta := fs.meta_map[parent_id];

        if parent_dir == p {
          assert ValidPath(fs, parent_dir);
          assert false;
        }

        assert parent_dir != p;
        assert ParentDirIsDir(fs, p); // observe

        if parent_id == id {
          assert false;
        }
      }
    }

    forall id | fs'.meta_map[id] != EmptyMetaData()
    ensures NoUnknownLinks(fs', id)
    {
      if id == fs.path_map[path] {
        var m := fs.meta_map[id];
        if m.nlink == 1 {
          assert fs'.meta_map[id] == EmptyMetaData();
          assert false;
        } else {
          var m' := fs'.meta_map[id];

          assert path !in m'.paths by {
            assert ValidLinks(fs, path);
            RemovePathCorrect(m.paths, path);
          }

          forall p | p !in m'.paths
          ensures fs'.path_map[p] != id
          {
            if p == path {
              assert fs'.path_map[p] == DefaultId;
            }
          }
        }
      }
    }
    assert Inv(fs');
  }

  lemma RenamePreservesInv(fs: FileSys, fs': FileSys, source: Path, dest: Path, ctime: Time)
  requires Inv(fs)
  requires Rename(fs, fs', source, dest, ctime)
  ensures Inv(fs')
  {
    assume Inv(fs');
  }

  lemma LinkPreservesInv(fs: FileSys, fs': FileSys, source: Path, dest: Path, ctime: Time)
  requires Inv(fs)
  requires Link(fs, fs', source, dest, ctime)
  ensures Inv(fs')
  {
    assume Inv(fs');
  }

  lemma SimpleStepPreservesInv(fs: FileSys, fs': FileSys, step: Step)
  requires Inv(fs)
  requires NextStep(fs, fs', step)
  requires step.CreateStep? || step.SymLinkStep? || step.ChangeAttrStep? 
        || step.TruncateStep? || step.WriteStep? || step.UpdateTimeStep?
  ensures Inv(fs')
  {
    var path := if step.SymLinkStep? then step.dest else step.path;

    forall p
    ensures ConsistentData(fs', p)
    ensures ValidLinks(fs', p)
    ensures ValidPath(fs', p) && p != RootDir ==> ParentDirIsDir(fs, p)
    {
      if p != path {
        assert ConsistentData(fs, p); // observe
        assert ValidLinks(fs, p); // observe
      }
    }
    assert Inv(fs');
  }

  // assert WF(fs');
  // assert fs'.meta_map[DefaultId] == EmptyMetaData();
  // assert fs'.data_map[DefaultId] == EmptyData();
  // assert (forall p | ValidPath(fs', p) :: |p| > 0);
  // assert (forall p :: ValidLinks(fs', p));
  // assert (forall p :: ConsistentData(fs', p));
  // assert (forall path | ValidPath(fs', path) :: fs'.meta_map[fs'.path_map[path]] != EmptyMetaData());
  // assert (forall path | ValidPath(fs', path) && path != RootDir :: ParentDirIsDir(fs', path));
  // assume (forall id | fs'.meta_map[id] != EmptyMetaData() :: NoUnknownLinks(fs', id));
  // assert Inv(fs');
}