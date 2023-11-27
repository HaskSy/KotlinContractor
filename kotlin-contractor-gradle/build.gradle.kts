plugins {
    id("java-gradle-plugin")
    kotlin("jvm")
    id("com.github.gmazzo.buildconfig")
    id("com.gradle.plugin-publish")
}

dependencies {
    implementation(kotlin("gradle-plugin-api"))
    implementation(kotlin("stdlib-jdk8"))
    implementation(project(mapOf("path" to ":kotlin-contractor-plugin")))

    compileOnly("com.google.auto.service:auto-service:1.1.1")
}

buildConfig {
    val project = project(":kotlin-contractor-plugin")
    packageName(project.group.toString())
    buildConfigField("String", "KOTLIN_PLUGIN_ID", "\"${rootProject.extra["kotlin_plugin_id"]}\"")
    buildConfigField("String", "KOTLIN_PLUGIN_GROUP", "\"${project.group}\"")
    buildConfigField("String", "KOTLIN_PLUGIN_NAME", "\"${project.name}\"")
    buildConfigField("String", "KOTLIN_PLUGIN_VERSION", "\"${project.version}\"")

    val annotationProject = project(":kotlin-contractor-annotation")
    buildConfigField("String", "ANNOTATION_LIBRARY_GROUP", "\"${annotationProject.group}\"")
    buildConfigField("String", "ANNOTATION_LIBRARY_NAME", "\"${annotationProject.name}\"")
    buildConfigField("String", "ANNOTATION_LIBRARY_VERSION", "\"${annotationProject.version}\"")
    useKotlinOutput()
}

gradlePlugin {
    plugins {
        create("kotlin-contractor") {
            id = rootProject.extra["kotlin_plugin_id"] as String
            displayName = "Kotlin Contractor Plugin"
            description = "Kotlin Contractor Plugin"
            implementationClass = "$group.KotlinContractorGradlePlugin"
        }
    }
}
