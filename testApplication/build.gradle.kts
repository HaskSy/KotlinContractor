plugins {
    kotlin("jvm") version "1.9.20"
    id("com.google.devtools.ksp") version "1.9.20-1.0.14"
}

group = "org.example"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    ksp(project(":contractor"))
    implementation(project(":contractor"))
}

kotlin {
    jvmToolchain(8)
}

tasks.test {
    useJUnitPlatform()
}
