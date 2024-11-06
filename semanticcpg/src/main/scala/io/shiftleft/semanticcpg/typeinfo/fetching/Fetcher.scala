package io.shiftleft.semanticcpg.typeinfo.fetching

import io.shiftleft.semanticcpg.typeinfo.dependencies.DirectDependency
import io.shiftleft.semanticcpg.typeinfo.{PackageIdentifier, PackageMetadata}
import io.shiftleft.semanticcpg.typeinfo.version.Version

import java.nio.file.{Path, Paths}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future, blocking}
import scala.util.Try

/** ...
  *
  * All public methods return an array of bytes or some type containing arrays of bytes. These byte arrays represent the
  * data that was downloaded by deriving fetchers.
  */
abstract class Fetcher extends AutoCloseable {
  /** Much of fetching is building paths to resources and converting between different types of paths: paths that
    * generic fetching understands (e.g., path to version info or dependency files), paths that a specific fetcher
    * understands (e.g., git repo paths), and filesystem paths. To avoid mixing incompatible Path instances, instances
    * of ServerPath are given to abstract methods that deriving types should implement; these deriving types can use
    * ServerPaths as they are or convert between other fetcher-specific Path types.
    */
  protected final class ServerPath private (val path: Path) {
    def this(pid: PackageIdentifier) = {
      this(Paths.get(pid.platform.toString).resolve(pid.name))
    }

    def getMetaDataPath: ServerPath = {
      ServerPath(path.resolve("metadata").resolve("metadata.ion"))
    }

    def getDirectDepsPath(version: Version): ServerPath = {
      ServerPath(path.resolve("dependencies").resolve(version.toFetcherStr).resolve("direct.ion"))
    }

    def getTransitiveDepsPath(version: Version): ServerPath = {
      ServerPath(path.resolve("dependencies").resolve(version.toFetcherStr).resolve("transitive.ion"))
    }

    def getVersionPath(version: Version): ServerPath = {
      ServerPath(path.resolve(version.toFetcherStr))
    }

    def getTypeFilePath(typeName: String): ServerPath = {
      ServerPath(path.resolve(typeName + ".ion"))
    }
    
    def getParent: ServerPath = {
      ServerPath(path.getParent)
    }

    override def toString: String = path.toString
  }
  
  /** The metadata file contains a list of all versions stored stored for this package identifier
    */
  def fetchMetaData(pids: List[PackageIdentifier]): Future[List[(PackageIdentifier, FetcherResult)]] = {
    val infoFilePaths = pids.map(ServerPath(_).getMetaDataPath)
    Future {
      blocking {
        val downloadResults = downloadFiles(infoFilePaths)
        pids.zip(downloadResults).toList
      }
    }
  }

  /** Returns a map from type name -> an input stream to read data about this type. The type name keys are type short
    * names, the NAME property of a TYPE_DECL in a CPG.
    */
  def fetchTypeData(
    pid: PackageIdentifier,
    version: Version,
    typeNames: List[String]
  ): Future[List[(String, FetcherResult)]] = {
    val versionedPackageDir = ServerPath(pid).getVersionPath(version)
    val typePaths           = typeNames.map(versionedPackageDir.getTypeFilePath)
    Future {
      blocking {
        val downloadResults = downloadFiles(typePaths)
        typeNames.zip(downloadResults).toList
      }
    }
  }
  
  def fetchDirectDependencies(
    versionedPids: List[(PackageIdentifier, Version)]
  ): Future[List[((PackageIdentifier, Version), FetcherResult)]] = {
    val directDepPaths = versionedPids.map((pid, version) => ServerPath(pid).getDirectDepsPath(version))
    Future {
      blocking {
        val downloadResults = downloadFiles(directDepPaths)
        versionedPids.zip(downloadResults).toList
      }
    }
  }

  def fetchTransitiveDependencies(pid: PackageIdentifier, version: Version): Future[FetcherResult] = {
    val transitiveDepPath = ServerPath(pid).getTransitiveDepsPath(version)
    Future {
      blocking {
        val downloadResults = downloadFiles(List(transitiveDepPath))
        downloadResults.head
      }
    }
  }

  /** This method should be overridden by deriving fetchers. This method should guarantee that return(i) is the download
    * result for paths(i)
    */
  protected def downloadFiles(paths: List[ServerPath]): List[FetcherResult]
}
