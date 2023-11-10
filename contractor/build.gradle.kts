import org.jetbrains.kotlin.ir.backend.js.compile

plugins {
    kotlin("jvm") version "1.9.20"
}

group = "org.example"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    implementation(kotlin("reflect"))
    implementation("com.google.devtools.ksp:symbol-processing-api:1.9.20-1.0.14")
    implementation("com.squareup:kotlinpoet:1.14.2")
    implementation("com.squareup:kotlinpoet-ksp:1.14.2")

    testImplementation(kotlin("test"))
    implementation(kotlin("stdlib-jdk8"))
}

kotlin {
    jvmToolchain(8)
}

tasks.test {
    useJUnitPlatform()
}
