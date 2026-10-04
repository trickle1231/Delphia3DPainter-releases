#include "paintcore.h"

#include <QtMath>

#include <algorithm>
#include <cmath>

namespace PaintCore {

namespace {
qreal resolvedRadius(const BrushSnapshot &brush, const DabCommand &command)
{
    return qMax<qreal>(0.5, command.radius > 0.0
        ? command.radius : brush.radius * qBound(0.0, command.pressure, 1.0));
}

qreal resolvedRadiusY(const BrushSnapshot &brush, const DabCommand &command)
{
    return qMax<qreal>(0.5, command.radiusY > 0.0 ? command.radiusY : resolvedRadius(brush, command));
}

QPointF rotatedExtent(qreal radiusX, qreal radiusY, qreal rotationDegrees)
{
    const qreal radians = qDegreesToRadians(rotationDegrees);
    const qreal cosine = std::cos(radians);
    const qreal sine = std::sin(radians);
    return {std::sqrt(radiusX * radiusX * cosine * cosine + radiusY * radiusY * sine * sine),
            std::sqrt(radiusX * radiusX * sine * sine + radiusY * radiusY * cosine * cosine)};
}

struct DabGeometry {
    qreal radiusX = 0.5;
    qreal radiusY = 0.5;
    qreal cosine = 1.0;
    qreal sine = 0.0;
};

DabGeometry prepareGeometry(const BrushSnapshot &brush, const DabCommand &command)
{
    const qreal radians = qDegreesToRadians(command.rotationDegrees);
    return {resolvedRadius(brush, command), resolvedRadiusY(brush, command),
            std::cos(radians), std::sin(radians)};
}

qreal textureCoverage(const BrushSnapshot &brush, qreal localX, qreal localY,
                      qreal radiusX, qreal radiusY)
{
    if (brush.textureTip.isNull()) return -1.0;
    const qreal u = qBound(0.0, (localX / radiusX + 1.0) * 0.5, 1.0);
    const qreal v = qBound(0.0, (localY / radiusY + 1.0) * 0.5, 1.0);
    const int x = qBound(0, qRound(u * (brush.textureTip.width() - 1)), brush.textureTip.width() - 1);
    const int y = qBound(0, qRound(v * (brush.textureTip.height() - 1)), brush.textureTip.height() - 1);
    const QRgb pixel = brush.textureTip.pixel(x, y);
    const qreal sample = brush.textureUsesAlpha ? qAlpha(pixel) / 255.0
                                                 : 1.0 - qGray(pixel) / 255.0;
    return std::pow(qBound(0.0, sample, 1.0), qMax<qreal>(0.01, brush.textureGamma));
}

qreal analyticCoverage(const BrushSnapshot &brush, const QPointF &pixelCenter,
                       const DabCommand &command, const DabGeometry &geometry)
{
    if (brush.hasSelectionClip
        && !brush.selectionClip.contains(QPoint(qFloor(pixelCenter.x()), qFloor(pixelCenter.y())))) {
        return 0.0;
    }
    const qreal dx = pixelCenter.x() - command.center.x();
    const qreal dy = pixelCenter.y() - command.center.y();
    const qreal localX = geometry.cosine * dx + geometry.sine * dy;
    const qreal localY = -geometry.sine * dx + geometry.cosine * dy;
    const qreal textured = textureCoverage(brush, localX, localY, geometry.radiusX, geometry.radiusY);
    if (textured >= 0.0) return textured;
    const qreal distance = std::hypot(localX / geometry.radiusX, localY / geometry.radiusY);
    if (distance >= 1.0) return 0.0;
    const qreal edge = qMin<qreal>(1.0, 1.0 / qMin(geometry.radiusX, geometry.radiusY));
    const qreal solid = qBound(0.0, brush.hardness, 1.0) * (1.0 - edge);
    if (distance <= solid) return 1.0;
    const qreal t = qBound(0.0, (distance - solid) / qMax<qreal>(1e-6, 1.0 - solid), 1.0);
    return 1.0 - t * t * (3.0 - 2.0 * t);
}
}

uint qHash(const TileKey &key, uint seed) noexcept
{
    return ::qHash((quint64(quint32(key.x)) << 32) | quint32(key.y), seed);
}

TileStore::TileStore(int tileSize)
    : m_tileSize(qMax(16, tileSize))
{
}

void TileStore::reset(const QSize &size)
{
    m_size = size.expandedTo(QSize());
    m_tiles.clear();
    m_active = false;
}

void TileStore::begin(const BrushSnapshot &brush)
{
    m_brush = brush;
    m_tiles.clear();
    m_active = brush.strokeId != 0 && brush.radius > 0.0 && !m_size.isEmpty();
}

QRect TileStore::tileRect(const TileKey &key) const
{
    return QRect(key.x * m_tileSize, key.y * m_tileSize, m_tileSize, m_tileSize)
        .intersected(QRect(QPoint(), m_size));
}

TileStore::Tile *TileStore::ensureTile(const TileKey &key)
{
    auto it = m_tiles.find(key);
    if (it != m_tiles.end()) return &it.value();
    const QRect rect = tileRect(key);
    if (rect.isEmpty()) return nullptr;
    Tile tile;
    tile.coverage = QImage(rect.size(), QImage::Format_Grayscale8);
    tile.coverage.fill(0);
    return &m_tiles.insert(key, std::move(tile)).value();
}

qreal TileStore::coverageAt(const QPointF &pixelCenter, const DabCommand &command) const
{
    return analyticCoverage(m_brush, pixelCenter, command, prepareGeometry(m_brush, command));
}

bool TileStore::apply(const DabCommand &command)
{
    if (!m_active || command.generation != m_brush.generation) return false;
    const qreal radiusX = resolvedRadius(m_brush, command);
    const qreal radiusY = resolvedRadiusY(m_brush, command);
    const QPointF extent = rotatedExtent(radiusX, radiusY, command.rotationDegrees);
    const QRect bounds = QRectF(command.center - extent, QSizeF(extent.x() * 2.0, extent.y() * 2.0))
        .toAlignedRect().intersected(QRect(QPoint(), m_size));
    if (bounds.isEmpty()) return true;
    for (int y = bounds.top() / m_tileSize; y <= bounds.bottom() / m_tileSize; ++y) {
        for (int x = bounds.left() / m_tileSize; x <= bounds.right() / m_tileSize; ++x) {
            const TileKey key{x, y};
            Tile *tile = ensureTile(key);
            // A tile naturally has sequence gaps for dabs that touched other
            // tiles. Its local invariant is strictly increasing, not global
            // contiguity.
            if (!tile || (tile->hasSequence && command.sequence <= tile->lastSequence)) return false;
            if (!tile->touched) { tile->before = tile->coverage.copy(); tile->touched = true; }
            const QRect overlap = bounds.intersected(tileRect(key));
            const QPoint origin = tileRect(key).topLeft();
            for (int py = overlap.top(); py <= overlap.bottom(); ++py) {
                uchar *row = tile->coverage.scanLine(py - origin.y());
                for (int px = overlap.left(); px <= overlap.right(); ++px) {
                    const qreal source = coverageAt(QPointF(px + 0.5, py + 0.5), command)
                        * m_brush.flow * qBound(0.0, command.opacity, 1.0);
                    const int alpha = qBound(0, qRound(source * 255.0), 255);
                    const int opacityCap = qBound(0, qRound(m_brush.opacity * 255.0), 255);
                    const int previous = row[px - origin.x()];
                    row[px - origin.x()] = uchar(qMin(opacityCap,
                        alpha + (previous * (255 - alpha) + 127) / 255));
                }
            }
            tile->lastSequence = command.sequence;
            tile->hasSequence = true;
        }
    }
    return true;
}

QVector<TileDelta> TileStore::finish()
{
    QVector<TileDelta> result;
    if (!m_active) return result;
    result.reserve(m_tiles.size());
    for (auto it = m_tiles.cbegin(); it != m_tiles.cend(); ++it) {
        if (it->touched) result.push_back({it.key(), it->before, it->coverage});
    }
    m_active = false;
    return result;
}

void TileStore::discard()
{
    m_tiles.clear();
    m_active = false;
}

QImage TileStore::tile(const TileKey &key) const
{
    const auto it = m_tiles.constFind(key);
    return it == m_tiles.cend() ? QImage() : it->coverage;
}

QVector<TileKey> TileStore::dirtyTiles() const
{
    QVector<TileKey> result;
    result.reserve(m_tiles.size());
    for (auto it = m_tiles.cbegin(); it != m_tiles.cend(); ++it) if (it->touched) result.push_back(it.key());
    return result;
}

void CommandStream::begin(BrushSnapshot snapshot)
{
    m_snapshot = std::move(snapshot);
    m_commands.clear();
    m_nextSequence = 0;
    m_active = m_snapshot.strokeId != 0;
}

bool CommandStream::append(const QPointF &center, qreal pressure, qreal resolvedRadius,
                            qreal resolvedRadiusY, qreal resolvedOpacity,
                            qreal resolvedRotationDegrees)
{
    if (!m_active || !qIsFinite(center.x()) || !qIsFinite(center.y())) return false;
    m_commands.push_back({m_snapshot.generation, m_nextSequence++, center,
                           qBound(0.0, pressure, 1.0), qMax<qreal>(0.0, resolvedRadius),
                           qMax<qreal>(0.0, resolvedRadiusY),
                           qBound(0.0, resolvedOpacity, 1.0), resolvedRotationDegrees});
    return true;
}

bool CommandStream::appendCoveragePatch(const QPoint &origin, const QImage &coverage)
{
    if (!m_active || coverage.isNull()) return false;
    DabCommand command;
    command.generation = m_snapshot.generation;
    command.sequence = m_nextSequence++;
    command.patchOrigin = origin;
    command.coveragePatch = coverage.copy();
    m_commands.push_back(std::move(command));
    return true;
}

void CommandStream::clear()
{
    m_commands.clear();
    m_snapshot = {};
    m_nextSequence = 0;
    m_active = false;
}

QVector<TileWork> scheduleTiles(const QVector<DabCommand> &commands, const QSize &surfaceSize,
                                int tileSize, qreal fallbackRadius)
{
    QHash<TileKey, QVector<int>> buckets;
    const int size = qMax(16, tileSize);
    const QRect surface(QPoint(), surfaceSize);
    for (int index = 0; index < commands.size(); ++index) {
        const DabCommand &command = commands.at(index);
        if (!command.coveragePatch.isNull()) {
            const QRect bounds(command.patchOrigin, command.coveragePatch.size());
            const QRect clipped = bounds.intersected(surface);
            if (clipped.isEmpty()) continue;
            for (int y = clipped.top() / size; y <= clipped.bottom() / size; ++y)
                for (int x = clipped.left() / size; x <= clipped.right() / size; ++x)
                    buckets[TileKey{x, y}].push_back(index);
            continue;
        }
        const qreal radiusX = qMax<qreal>(0.5, command.radius > 0.0 ? command.radius : fallbackRadius);
        const qreal radiusY = qMax<qreal>(0.5, command.radiusY > 0.0 ? command.radiusY : radiusX);
        const QPointF extent = rotatedExtent(radiusX, radiusY, command.rotationDegrees);
        const QRect bounds = QRectF(command.center - extent, QSizeF(extent.x() * 2.0, extent.y() * 2.0))
            .toAlignedRect().intersected(surface);
        if (bounds.isEmpty()) continue;
        for (int y = bounds.top() / size; y <= bounds.bottom() / size; ++y)
            for (int x = bounds.left() / size; x <= bounds.right() / size; ++x)
                buckets[TileKey{x, y}].push_back(index);
    }
    QVector<TileWork> work;
    work.reserve(buckets.size());
    for (auto it = buckets.cbegin(); it != buckets.cend(); ++it)
        work.push_back({it.key(), it.value()});
    std::sort(work.begin(), work.end(), [](const TileWork &a, const TileWork &b) {
        return a.key.y == b.key.y ? a.key.x < b.key.x : a.key.y < b.key.y;
    });
    return work;
}

TileResult executeTile(const TileWork &work, const QVector<DabCommand> &commands,
                       const BrushSnapshot &brush, const QSize &surfaceSize, int tileSize)
{
    TileResult result;
    result.key = work.key;
    const int size = qMax(16, tileSize);
    const QRect rect(work.key.x * size, work.key.y * size, size, size);
    const QRect clipped = rect.intersected(QRect(QPoint(), surfaceSize));
    if (clipped.isEmpty() || work.commandIndices.isEmpty()) return result;
    result.coverage = QImage(clipped.size(), QImage::Format_Grayscale8);
    result.coverage.fill(0);
    bool hasCommand = false;
    quint64 previous = 0;
    for (const int index : work.commandIndices) {
        if (index < 0 || index >= commands.size()) { result.coverage = QImage(); return result; }
        const DabCommand &command = commands.at(index);
        if (command.generation != brush.generation || (hasCommand && command.sequence <= previous)) {
            result.coverage = QImage(); return result;
        }
        if (!command.coveragePatch.isNull()) {
            const QRect patchRect(command.patchOrigin, command.coveragePatch.size());
            const QRect patchBounds = patchRect.intersected(clipped);
            for (int y = patchBounds.top(); y <= patchBounds.bottom(); ++y) {
                uchar *row = result.coverage.scanLine(y - clipped.top());
                for (int x = patchBounds.left(); x <= patchBounds.right(); ++x) {
                    const int alpha = qAlpha(command.coveragePatch.pixel(x - command.patchOrigin.x(),
                                                                         y - command.patchOrigin.y()));
                    const int localX = x - clipped.left();
                    row[localX] = uchar(alpha + (row[localX] * (255 - alpha) + 127) / 255);
                }
            }
            if (!hasCommand) result.firstSequence = command.sequence;
            result.lastSequence = command.sequence;
            previous = command.sequence;
            hasCommand = true;
            continue;
        }
        const DabGeometry geometry = prepareGeometry(brush, command);
        const QPointF extent = rotatedExtent(geometry.radiusX, geometry.radiusY, command.rotationDegrees);
        const QRect dabBounds = QRectF(command.center - extent, QSizeF(extent.x() * 2, extent.y() * 2))
            .toAlignedRect().intersected(clipped);
        for (int y = dabBounds.top(); y <= dabBounds.bottom(); ++y) {
            uchar *row = result.coverage.scanLine(y - clipped.top());
            for (int x = dabBounds.left(); x <= dabBounds.right(); ++x) {
                const int alpha = qBound(0, qRound(analyticCoverage(brush, QPointF(x + .5, y + .5), command, geometry)
                    * brush.flow * qBound(0.0, command.opacity, 1.0) * 255.0), 255);
                const int localX = x - clipped.left();
                const int opacityCap = qBound(0, qRound(brush.opacity * 255.0), 255);
                row[localX] = uchar(qMin(opacityCap,
                    alpha + (row[localX] * (255 - alpha) + 127) / 255));
            }
        }
        if (!hasCommand) result.firstSequence = command.sequence;
        result.lastSequence = command.sequence;
        previous = command.sequence;
        hasCommand = true;
    }
    return result;
}

} // namespace PaintCore
