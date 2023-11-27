buildscript {
    extra["kotlin_plugin_id"] = "org.example.contractor.$name"
}

plugins {
    kotlin("jvm") version "1.9.10" apply false
//    id("org.jetbrains.dokka") version "1.9.10" apply false
    id("com.gradle.plugin-publish") version "1.0.0" apply false
    id("com.github.gmazzo.buildconfig") version "4.1.2" apply false
}

allprojects {
    group = "org.example.contractor"
    version = "0.1"
}

subprojects {
    repositories {
        mavenCentral()
    }
}
