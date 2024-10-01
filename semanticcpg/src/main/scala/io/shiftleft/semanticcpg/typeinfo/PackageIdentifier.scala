package io.shiftleft.semanticcpg.typeinfo

enum LanguagePlatform {
  case Java
  override def toString: String = this match
    case Java => "java"
    case _    => throw new RuntimeException(s"no toString override for LanguageFrontend enum constant value")
}

object LanguagePlatform {
  def ofString(str: String): LanguagePlatform = str match
    case "java" => LanguagePlatform.Java
    case _      => throw new RuntimeException(s"couldn't convert string to LanguageFrontend: $str")
}

/** Type representing all info needed by the fetcher to download and identify type info for a package
  */
final case class PackageIdentifier(platform: LanguagePlatform, name: String)
